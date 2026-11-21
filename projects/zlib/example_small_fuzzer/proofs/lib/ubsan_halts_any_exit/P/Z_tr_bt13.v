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

Module Z_tr_bt1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Ltac h32_store ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u32arr_store_ok psegs _ A (av32 a n) idx (wa (A + 4 * idx)) ARR ltac:(rewrite av32_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le4 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av32_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      replace (A + 4 * idx) with E in ARR' by lia;
      let LN := fresh "L32" in pose proof (av32_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNH" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Definition bt1R (L : dlay) (T E n mc dsc stp : Z) (ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz (T + 4 * E + 2)) t1 t2 s0 (wz (dl_As L)) a0 (wz dsc) (wz stp) (wz 4096) (wz n) (wz (dl_As L + 3008)) (wz (dl_As L + 5308 + n)) (wz (T + 4 * n + 2))
      (wz T) (wz mc) (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Notation Wbt1 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).

Definition bt_loop1_post (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc stp : Z) (FC BC : arr) (HM OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 DL' HP' HL' DP' mc' m',
    ms' = MS (bt1R L T (sd_elems t) (sd_elems t) mc' dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b9a8) fc None m' (seg_rom psegs)
    /\ munch (Wbt1 L T N) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL'); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL' HP' HL' HM DP' BC OL SL MC, mc')
    /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ 0 <= HL' <= sd_elems t /\ -1 <= mc' < sd_elems t.

Lemma bt_loop1 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc stp : Z) (FC BC : arr) (HM OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (DL HP : arr) (HL : Z) (DP : arr) (n mc : Z)
    (ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  mem_inv psegs m -> dlay_ok L -> munch (Wbt1 L T N) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> sd_elems t < N -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) ->
  0 <= HL <= n -> 0 <= n -> Z.of_nat (S f) = sd_elems t - n -> -1 <= mc < sd_elems t ->
  R = L1 t (bt_upd s t FC DL HP HL HM DP BC OL SL MC) n mc ->
  evt psegs (bt_loop1_post L s t T N dsc stp FC BC HM OL SL MC R ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (bt1R L T (sd_elems t) n mc dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b970) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA DPA GC MI LAY MU WM RT1 RT2 REN LFC LDL LHP LDP RFC RHL Rn Ef Rmc ER.
  all: pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t) as RE.
  all: lay_open LAY.
  all: rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1_step in ER by lia.
  all: pose proof (RFC n ltac:(lia)) as Rf.
  all: pose proof (u16arr_read psegs m T (avct FC DL N) (2 * n) _ (wa (T + 4 * n + 2 + -2)) ARR (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
  all: pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  all: unfold bt1R; zs2; rewrite zx16_small by lia; zstep; br_cases_s K.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K) in ER. cbn [negb] in ER.
    ct_store_dl ARR FC DL N T n (wrap16 0) ltac:(reflexivity).
    zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (dl_As L + 5308 + n + 1) (dl_As L + 5308 + (n + 1)).
    zstep. br_cases_s K2; [|exfalso; lia].
    replace (n + 1) with (sd_elems t) in * by lia. rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1_end in ER.
    apply evt_done. unfold bt_loop1_post, bt1R. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [exact ER|]. rewrite ?arr_len_set. repeat split; lia.
  -
    rewrite (proj2 (Z.eqb_neq _ _) K) in ER. cbn [negb] in ER.
    zs2. zs2. zs2. shl_norm. zs2. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) n ltac:(reflexivity).
    pb_store DPA DP 573 (dl_As L + 5308) n (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (dl_As L + 5308 + n + 1) (dl_As L + 5308 + (n + 1)).
    zstep. br_cases_s K2; [exfalso; lia|].
    replace (n + 1) with (sd_elems t) in * by lia. rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.L1_end in ER.
    apply evt_done. unfold bt_loop1_post, bt1R. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [exact ER|]. rewrite ?arr_len_set. repeat split; lia.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K) in ER. cbn [negb] in ER.
    ct_store_dl ARR FC DL N T n (wrap16 0) ltac:(reflexivity).
    zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (dl_As L + 5308 + n + 1) (dl_As L + 5308 + (n + 1)).
    zstep. br_cases_s K2; [exfalso; lia|].
    eapply (IH L s t T N dsc stp FC BC HM OL SL MC R m0 (arr_set DL n (wrap16 0)) HP HL DP (n + 1) mc);
      [exact ARR| exact HPA| exact DPA| exact GC| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact REN| exact LFC| rewrite arr_len_set; exact LDL
      | exact LHP| exact LDP| exact RFC| lia| lia| lia| exact Rmc| exact ER].
  -
    rewrite (proj2 (Z.eqb_neq _ _) K) in ER. cbn [negb] in ER.
    zs2. zs2. zs2. shl_norm. zs2. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) n ltac:(reflexivity).
    pb_store DPA DP 573 (dl_As L + 5308) n (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (dl_As L + 5308 + n + 1) (dl_As L + 5308 + (n + 1)).
    zstep. br_cases_s K2; [|exfalso; lia].
    eapply (IH L s t T N dsc stp FC BC HM OL SL MC R m0 DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0)) (n + 1) n);
      [exact ARR| exact HPA| exact DPA| exact GC| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact REN| exact LFC| exact LDL
      | rewrite arr_len_set; exact LHP| rewrite arr_len_set; exact LDP| exact RFC| lia| lia| lia| lia| exact ER].
Qed.
End Z_tr_bt1.


Module Z_tr_bt2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition bD_cells (L : dlay) (s : deflate_state) (OL SL : Z) (h0 h1 h2 h3 h4 : list byte) : list cell :=
  [CB 7 h0; C8 (wz (dl_Ab L + ds_lit_bufsize s)); C4 (wz (ds_lit_bufsize s)); C4 (wz (ds_sym_next s)); C4 (wz (ds_sym_end s)); CB 4 h1;
   C8 (wz OL); C8 (wz SL); C4 (wz (ds_matches s)); C4 (wz (ds_insert s)); C2 (wz (ds_bi_buf s)); CB 2 h2; C4 (wz (ds_bi_valid s)); CB 4 h3; C4 (wz 0); C8 (wz (ds_high_water s)); CB 4 h4; C4 (wz 0)].

Definition bt2R (L : dlay) (T HL mc dsc stp : Z) (ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz mc) t1 t2 s0 (wz (dl_As L)) a0 (wz dsc) (wz stp) (wz 2) (wz HL) (wz (dl_As L + 3008)) (wz (dl_As L + 5308)) (wz 1)
      (wz T) (wz mc) (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma lxor_sign : forall a, 0 <= a < 2^63 -> Z.lxor a (2^63) = a + 2^63.
Proof.
  intros a H. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 63 n) as [<-|]; [|apply andb_false_r].
  rewrite andb_true_r. rewrite Z.testbit_false by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma l2node_mask : forall mc, -1 <= mc < 2^31 - 1 ->
  Z.land ((0 - Z.b2z (Z.lxor (mc mod 18446744073709551616) 9223372036854775808 <? 9223372036854775810)) mod 18446744073709551616) (mc + 1)
  = (if mc <? 2 then mc + 1 else 0).
Proof.
  intros mc H. destruct (Z.eq_dec mc (-1)) as [->|N1]; [reflexivity|]. destruct (Z.eq_dec mc 0) as [->|N0]; [reflexivity|]. destruct (Z.eq_dec mc 1) as [->|N2]; [reflexivity|].
  rewrite (Z.mod_small mc) by lia. change 9223372036854775808 with (2^63). rewrite lxor_sign by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_ge mc 2)) by lia. reflexivity.
Qed.

Lemma l2node_mask_ge : forall mc, 2 <= mc < 2^31 - 1 ->
  Z.land ((0 - Z.b2z (Z.lxor mc 9223372036854775808 <? 9223372036854775810)) mod 18446744073709551616) (mc + 1) = 0.
Proof.
  intros mc H. change 9223372036854775808 with (2^63). rewrite lxor_sign by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma swrap32_succ_m1 : forall mc, -1 <= mc < 2^31 - 1 -> bv_swrap 32 (mc mod 18446744073709551616 + 1) = mc + 1.
Proof.
  intros mc H. destruct (Z.eq_dec mc (-1)) as [->|NE]; [reflexivity|].
  rewrite Z.mod_small by lia. apply Z_dkit.bv_swrap32_id. lia.
Qed.

Definition stree_view (t : tree_id) (stp : Z) : Prop :=
  (stp = 0 /\ stree_has t = false)
  \/ (0 < stp < 2^32 /\ stree_has t = true
      /\ forall mm node, mem_inv psegs mm -> 0 <= node < 3 ->
           ov_read_bytes psegs mm (wa (stp + node * 4 + 2)) 2 = Some (le2 (wz (stree_Len t node))) /\ 0 <= stree_Len t node < 16).

Notation Wbt2 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5968)] (only parsing).

Definition bt_l2_post (L : dlay) (s : deflate_state) (T N dsc stp : Z) (FC DL HP : arr) (HL HM : Z) (DP : arr) (OL SL mc : Z)
    (ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 h0 h1 h2 h3 h4 pcx m',
    ms' = MS (bt2R L T HL mc dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wbt2 L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4)
    /\ ((pcx = 0x1c1c0 /\ HL < 2) \/ (pcx = 0x1b9b4 /\ 2 <= HL)).

Ltac l2_close MU WM ARR HPA DPA GC GD :=
  let K3 := fresh "K3" in
  zs2; zs2; zstep; br_cases K3;
  (apply evt_done; unfold bt_l2_post, bt2R, bD_cells; do 9 eexists;
   split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ARR|]; split; [exact HPA|]; split; [exact DPA|];
   split; [exact GC|]; split; [close_cells GD|];
   first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]]).

Lemma bt_l2_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc dsc stp HM OL SL node mc' : Z) (FC DL HP DP : arr) (h0 h1 h2 h3 h4 : list byte)
    (ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 3 <= N -> arr_len FC = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  stree_view t stp -> 0 <= HL < 2 -> -1 <= mc < 286 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  (node, mc') = l2node mc ->
  evt psegs (bt_l2_post L s T N dsc stp (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node) (HL + 1) HM (arr_set DP node (wrap8 0))
               (wrap64 (OL - 1)) (if stree_has t then wrap64 (SL - stree_Len t node) else SL) mc'
               ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (bt2R L T HL mc dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c1c0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA GC GD MI LAY RT1 RT2 RN LFC LHP LDP SV RHL Rmc ROL RSL ENODE.
  pose proof (munch_refl (Wbt2 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. unfold bt2R, bD_cells in *.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  assert (En : node = (if mc <? 2 then mc + 1 else 0) /\ mc' = (if mc <? 2 then mc + 1 else mc)).
  { unfold l2node in ENODE. destruct (mc <? 2); inversion ENODE; auto. }
  destruct En as [En Emc']. assert (Rnode : 0 <= node < 3) by (rewrite En; destruct (Z.ltb_spec mc 2); lia).
  zs2. rewrite swrap32_succ_m1 by lia. zs2. zstep.
  br_cases K.
  -
    rewrite (proj2 (Z.ltb_lt _ _) K) in En, Emc'. subst node mc'.
    zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2. rewrite l2node_mask by lia. rewrite (proj2 (Z.ltb_lt _ _) K).
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) (mc + 1) ltac:(reflexivity).
    zs2. shl_norm. zs2. zs2.
    ct_store_fc ARR FC DL N T (mc + 1) (wrap16 1) ltac:(reflexivity).
    pb_store DPA DP 573 (dl_As L + 5308) (mc + 1) (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2.
    zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
    + subst stp. br_true. l2_close MU WM ARR HPA DPA GC GD.
    + br_false. destruct (RDS m0 (mc + 1) ltac:(eassumption) ltac:(lia)) as [RDl Rsl].
      zs2. zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2. l2_close MU WM ARR HPA DPA GC GD.
  -
    rewrite (proj2 (Z.ltb_ge _ _)) in En, Emc' by lia. subst node mc'.
    zs2.
    zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2. rewrite l2node_mask_ge by lia.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) 0 ltac:(reflexivity).
    zs2. zs2. zs2.
    ct_store_fc ARR FC DL N T 0 (wrap16 1) ltac:(reflexivity).
    pb_store DPA DP 573 (dl_As L + 5308) 0 (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2.
    zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
    + subst stp. br_true. l2_close MU WM ARR HPA DPA GC GD.
    + br_false. destruct (RDS m0 0 ltac:(eassumption) ltac:(lia)) as [RDl Rsl]. change (0 * 4) with 0 in RDl. replace (stp + 0 + 2) with (stp + 2) in RDl by lia.
      zs2. zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2. l2_close MU WM ARR HPA DPA GC GD.
Qed.
End Z_tr_bt2.


Module Z_tr_bt3.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition pqR1 (L : dlay) (T k x6v x7v hlv v n : Z) (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz k) (wz x6v) (wz x7v) s0 (wz (dl_As L)) a0 a1 (wz (dl_As L + 5308)) (wz 1) (wz n) (wz v) (wz (dl_As L + 5308 + v)) (wz (T + v * 4))
      (wz T) s3 (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 (wz hlv) t4 t5 t6.

Lemma lor1_even : forall q, 0 <= q -> Z.lor (2 * q) 1 = 2 * q + 1.
Proof.
  intros q Hq. pose proof (Z.add_lor_land (2 * q) 1) as H.
  assert (E : Z.land (2 * q) 1 = 0).
  { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  lia.
Qed.

Lemma pq1_sel : forall (L : dlay) (T N k j q HL v n : Z) (FC DL HP DP : arr) (x7v : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= j <= HL -> HL < 573 ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv',
               ms' = MS (pqR1 L T k (sel3 FC HL DP HP j) (sel3 FC HL DP HP j) hlv' v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4' t5' t6') F (wz 0x1bab4) fc None m (seg_rom psegs))
      (MS (pqR1 L T k j x7v HL v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1ba48) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Ej Rj RHL. lay_open LAY. unfold pqR1.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zstep. br_cases K.
  -
    zs2. apply evt_done. unfold sel3. rewrite (proj2 (Z.ltb_ge j HL)) by lia. cbn [andb]. do 4 eexists. reflexivity.
  - pose proof (PQ j ltac:(lia)) as Rhj. pose proof (PQ (j + 1) ltac:(lia)) as Rhj1.
    pose proof (u32arr_read psegs m _ (av32 HP 573) j _ (wa (dl_As L + 3008 + j * 4)) HPA (av32_nth HP 573 j ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
    pose proof (u32arr_read psegs m _ (av32 HP 573) (j + 1) _ (wa (dl_As L + 3008 + (j + 1) * 4)) HPA (av32_nth HP 573 (j + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj1.
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j) ltac:(lia)) as [RDfj _].
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP (j + 1)) ltac:(lia)) as [RDfj1 _].
    replace (T + 4 * arr_get HP j) with (T + arr_get HP j * 4) in RDfj by lia. replace (T + 4 * arr_get HP (j + 1)) with (T + arr_get HP (j + 1) * 4) in RDfj1 by lia.
    pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rhj1) as Rfj1.
    zs2. replace (Z.lor j 1) with (j + 1) by (rewrite Ej, lor1_even by lia; lia).
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. zs2.
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. rewrite (zx16_small (arr_get FC (arr_get HP (j + 1)))) by lia. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j))) by lia.
    zstep. br_cases K1.
    +
      zstep. br_cases_s K2.
      *
        zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
        cbn [andb orb]. do 4 eexists. reflexivity.
      *
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP j) _ (wa (dl_As L + 5308 + arr_get HP j)) DPA (av8_nth DP 573 (arr_get HP j) ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP (j + 1)) _ (wa (dl_As L + 5308 + arr_get HP (j + 1))) DPA (av8_nth DP 573 (arr_get HP (j + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RDdj1.
        pose proof (RDP (arr_get HP j) ltac:(lia)) as Rdj. pose proof (RDP (arr_get HP (j + 1)) ltac:(lia)) as Rdj1.
        zs2. zs2. zsb. rewrite (bv8_small (arr_get DP (arr_get HP (j + 1)))) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j))) by lia.
        zs2. zstep. br_cases K3.
        -- zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
        -- zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
    +
      zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      cbn [andb orb]. do 4 eexists. reflexivity.
Qed.

Lemma pq1_cmp : forall (L : dlay) (T N k j' HL v n : Z) (FC DL HP DP : arr) (hlv : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= j' <= HL -> HL < 573 -> 0 <= v < N ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv' pcx,
               ms' = MS (pqR1 L T k (arr_get HP j') j' hlv' v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4' t5' t6') F (wz pcx) fc None m (seg_rom psegs)
               /\ ((pcx = 0x1b9d8 /\ smal FC DP v (arr_get HP j') = true) \/ (pcx = 0x1ba28 /\ smal FC DP v (arr_get HP j') = false)))
      (MS (pqR1 L T k j' j' hlv v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bab4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Rj RHL Rv. lay_open LAY. unfold pqR1.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (PQ j' Rj) as Rhj.
  pose proof (u32arr_read psegs m _ (av32 HP 573) j' _ (wa (dl_As L + 3008 + j' * 4)) HPA (av32_nth HP 573 j' ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j') ltac:(lia)) as [RDfj _].
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI v ltac:(lia)) as [RDfv _].
  replace (T + 4 * arr_get HP j') with (T + arr_get HP j' * 4) in RDfj by lia. replace (T + 4 * v) with (T + v * 4) in RDfv by lia.
  pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rv) as Rfv.
  zs2. shl_norm. zs2. zs2. zs2. rewrite (zx16_small (arr_get FC v)) by lia. zs2. shl_norm. zs2. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j'))) by lia.
  zstep. br_cases K1.
  - apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - zstep. br_cases_s K2.
    + apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
    + pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP j') _ (wa (dl_As L + 5308 + arr_get HP j')) DPA (av8_nth DP 573 (arr_get HP j') ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
      pose proof (u8arr_read psegs m _ (av8 DP 573) v _ (wa (dl_As L + 5308 + v)) DPA (av8_nth DP 573 v ltac:(lia)) ltac:(lia) eq_refl) as RDdv.
      pose proof (RDP (arr_get HP j') ltac:(lia)) as Rdj. pose proof (RDP v ltac:(lia)) as Rdv.
      zs2. zsb. rewrite (bv8_small (arr_get DP v)) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j'))) by lia.
      zstep. br_cases K3.
      * apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
        rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
      * zs2. apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. apply orb_true_r.
Qed.

Definition fuel_ok (f : nat) (j HL : Z) : Prop := HL < j * 2 ^ Z.of_nat f.
Lemma fuel_ok_0 : forall j HL, fuel_ok 0 j HL -> HL < j.
Proof. unfold fuel_ok. intros j HL H. change (2 ^ Z.of_nat 0) with 1 in H. lia. Qed.
Lemma fuel_ok_S : forall f j j' HL, fuel_ok (S f) j HL -> 2 * j <= j' -> 0 < j -> fuel_ok f j' HL.
Proof.
  unfold fuel_ok. intros f j j' HL H Hj Hp. rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia.
  assert (0 < 2 ^ Z.of_nat f) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.
Lemma pq_out : forall f X t v k j, ds_heap_len X < j -> pqdownheap_loop f X t v k j = (X, k).
Proof. intros [|f] X t v k j H; [reflexivity|]. cbn [pqdownheap_loop]. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

Notation Wpq L := [(dl_As L + 3008, dl_As L + 5300)] (only parsing).

Definition pq1_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists k0 x6v hlv t4 t5 t6 HP' k' m',
    ms' = MS (pqR1 L T k0 x6v k' hlv v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1b9dc) fc None m' (seg_rom psegs)
    /\ munch (Wpq L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL HP' HL HM DP BC OL SL MC, k')
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N) /\ 1 <= k' <= HL.

Lemma pq1_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (HP : arr) (k j q x7v : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq L) m0 T FC DL N -> mem_inv psegs m -> dlay_ok L -> munch (Wpq L) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= k -> k < j -> j <= HL -> HL < 573 -> 0 <= v < N -> fuel_ok f j HL ->
  R = pqdownheap_loop f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t v k j ->
  evt psegs (pq1_post L s t T N HL HM v n FC DL DP BC OL SL MC R ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 F fc m0)
      (MS (pqR1 L T k j x7v HL v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1ba48) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM RT1 RT2 RN LHP PQ RFC RDP Ej Rk Rkj Rj RHL Rv FU ER.
  - apply fuel_ok_0 in FU. lia.
  - assert (RDTm : ct_readable [] m T FC DL N) by (eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; tauto]).
    pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.sel3_range FC HL DP HP j ltac:(lia)) as Rs3.
    rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.loop3_S_sel in ER by lia.
    eapply evt_cut; [eapply (pq1_sel L T N k j q HL v n FC DL HP DP x7v); try eassumption; lia|]. intros ms' (t4' & t5' & t6' & hlv' & ->).
    eapply evt_cut; [eapply (pq1_cmp L T N k (sel3 FC HL DP HP j) HL v n FC DL HP DP hlv'); try eassumption; lia|].
    intros ms' (t4'' & t5'' & t6'' & hlv'' & pcx & -> & [[-> SM]|[-> SM]]); rewrite SM in ER.
    +
      unfold pqR1. zs2.
      apply evt_done. unfold pq1_post, pqR1. do 9 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
      split; [exact ER|]. split; [exact LHP|]. split; [exact PQ| lia].
    +
      set (j' := sel3 FC HL DP HP j) in *.
      pose proof (PQ j' ltac:(lia)) as Rhj. lay_open LAY.
      pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
      unfold pqR1. zs2. zs2. shl_norm. zs2.
      h32_store HPA HP 573 (dl_As L + 3008) k (arr_get HP j') ltac:(reflexivity).
      zs2. zs2. shl_norm. strip32. zs2. zstep. br_cases K.
      *
        rewrite pq_out in ER by (rewrite bt_heap_len; lia).
        apply evt_done. unfold pq1_post, pqR1. do 9 eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
        split; [exact ER|]. split; [rewrite arr_len_set; exact LHP|]. split; [|lia].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
      * eapply (IH L s t T N HL HM v n FC DL DP BC OL SL MC R m0 (arr_set HP k (arr_get HP j')) j' (j' * 2) j' j');
          [exact HPA| exact DPA| exact GC| exact RDT| eassumption| assumption| exact MU| exact WM| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LHP
          | | exact RFC| exact RDP| lia| lia| lia| lia| exact RHL| exact Rv| eapply fuel_ok_S; [exact FU| lia| lia]| exact ER].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
Qed.

Definition l3R (L : dlay) (T n : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (wz (dl_As L)) a0 a1 (wz (dl_As L + 5308)) (wz 1) a4 (wz n) a6 a7
      (wz T) s3 (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma pqdownheap_flat : forall s t FC DL HP HL HM DP BC OL SL MC k,
  pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t k
  = heap_set (fst (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2)))
             (snd (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2))) (arr_get HP k).
Proof.
  intros. unfold pqdownheap. rewrite bt_heap_get. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  destruct (pqdownheap_loop 32 _ t (arr_get HP k) k (k * 2)); reflexivity.
Qed.
Lemma loop3_S : forall f X t n, 1 <= n -> build_tree_loop3 (S f) X t n = build_tree_loop3 f (pqdownheap X t n) t (n - 1).
Proof. intros. cbn [build_tree_loop3]. rewrite (proj2 (Z.leb_le 1 n)) by lia. reflexivity. Qed.
Lemma loop3_out : forall f X t n, n < 1 -> build_tree_loop3 f X t n = X.
Proof. intros [|f] X t n H; [reflexivity|]. cbn [build_tree_loop3]. rewrite (proj2 (Z.leb_gt 1 n)) by lia. reflexivity. Qed.

Definition l3_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n1 : Z) (FC DL DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 HP' pcx m',
    ms' = MS (l3R L T n1 ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wpq L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = build_tree_loop3 f (bt_upd s t FC DL HP' HL HM DP BC OL SL MC) t n1
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N)
    /\ ((pcx = 0x1b9f4 /\ 1 <= n1) \/ (pcx = 0x1baec /\ n1 = 0)).

Ltac l3_close MU WM HPA DPA GC ER LHP PQ Rv SIDE :=
  apply evt_done; unfold l3_post, l3R; do 13 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HPA|]; split; [eassumption|]; split; [eassumption|];
  split; [exact ER|]; split; [rewrite arr_len_set; exact LHP|]; split;
  [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
    match goal with |- 0 <= arr_get (arr_set _ ?k _) i < _ => destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi] end
  | SIDE; split; [reflexivity| lia] ].

Lemma l3_body : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq L) m0 T FC DL N -> mem_inv psegs m -> dlay_ok L -> munch (Wpq L) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= n <= HL -> HL < 573 ->
  R = build_tree_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t n ->
  evt psegs (l3_post L s t T N HL HM (n - 1) FC DL DP BC OL SL MC f R ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 F fc m0)
      (MS (l3R L T n ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b9f4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY MU WM RT1 RT2 RN LHP PQ RFC RDP Rn RHL ER.
  rewrite loop3_S, pqdownheap_flat in ER by lia.
  pose proof (PQ n ltac:(lia)) as Rv. pose proof LAY as LAY0. lay_open LAY0.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (u32arr_read psegs m _ (av32 HP 573) n _ (wa (dl_As L + 3008 + n * 4)) HPA (av32_nth HP 573 n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn.
  unfold l3R. zs2. zs2. shl_norm. zs2. zs2. zs2. zs2. shl_norm. strip32. zs2.
  zstep. br_cases K.
  -
    rewrite pq_out in ER by (rewrite bt_heap_len; lia). cbn [fst snd] in ER. rewrite bt_heap_set in ER.
    zs2. zs2. shl_norm. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) n (arr_get HP n) ltac:(reflexivity).
    zs2. reg_as (n + -1) (n - 1). zstep. br_cases K2.
    + l3_close MU WM HPA DPA GC ER LHP PQ Rv ltac:(right).
    + l3_close MU WM HPA DPA GC ER LHP PQ Rv ltac:(left).
  -
    zs2. zs2. shl_norm. zs2. zs2. zs2.
    call (pq1_loop 32 L s t T N HL HM (arr_get HP n) n FC DL DP BC OL SL MC
            (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP n) n (n * 2)) m HP n (n * 2) n n).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
    1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact Rv. }
    1:{ unfold fuel_ok. change (2 ^ Z.of_nat 32) with 4294967296. lia. } 1:{ reflexivity. }
    match goal with E : pqdownheap_loop _ _ _ _ _ _ = (bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, ?kk), H : u32arr psegs ?mm _ (av32 ?hp 573), HD : u8arr psegs ?mm _ (av8 DP 573),
                     HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      rewrite E in ER; cbn [fst snd] in ER; rewrite bt_heap_set in ER;
      rename H into HPB; rename HD into DPB; pose proof (av32_zlength hp 573 ltac:(lia)) as L32b;
      unfold pqR1; zs2; zs2; shl_norm; zs2;
      h32_store HPB hp 573 (dl_As L + 3008) kk (arr_get HP n) ltac:(reflexivity);
      zs2; reg_as (n + -1) (n - 1); zstep; br_cases K2;
      [ l3_close MU WM HPB DPB GC ER HL' HQ Rv ltac:(right) | l3_close MU WM HPB DPB GC ER HL' HQ Rv ltac:(left) ] end.
Qed.

Definition bt_loop3_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 HP' m',
    ms' = MS (l3R L T 0 ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1baec) fc None m' (seg_rom psegs)
    /\ munch (Wpq L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = bt_upd s t FC DL HP' HL HM DP BC OL SL MC
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N).

Lemma bt_loop3 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq L) m0 T FC DL N -> mem_inv psegs m -> dlay_ok L -> munch (Wpq L) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  Z.of_nat (S f) = n -> n <= HL -> HL < 573 ->
  R = build_tree_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t n ->
  evt psegs (bt_loop3_post L s t T N HL HM FC DL DP BC OL SL MC R ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 F fc m0)
      (MS (l3R L T n ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b9f4) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM RT1 RT2 RN LHP PQ RFC RDP Ef Rn RHL ER.
  - call (l3_body L s t T N HL HM n FC DL HP DP BC OL SL MC 0%nat R m).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
    1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact ER. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    match goal with E : R = build_tree_loop3 0 _ _ _ |- _ => cbn [build_tree_loop3] in E; rename E into ER' end.
    replace (n - 1) with 0 by lia.
    apply evt_done. unfold bt_loop3_post. do 12 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER'|]. split; assumption.
  - call (l3_body L s t T N HL HM n FC DL HP DP BC OL SL MC (S f) R m).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
    1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact ER. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    match goal with E : R = build_tree_loop3 (S f) _ _ _, HA : u32arr psegs ?mm _ (av32 ?hp 573), HD : u8arr psegs ?mm _ _, HG : rw_cells psegs ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N HL HM (n - 1) FC DL hp DP BC OL SL MC R m0);
        [exact HA| exact HD| exact HG| exact RDT| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact RN| assumption| assumption| exact RFC| exact RDP
        | lia| lia| exact RHL| exact E] end.
Qed.
End Z_tr_bt3.

Module Z_tr_bt4.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition pqR2 (L : dlay) (T k x6v x7v hlv v n : Z) (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz (dl_As L + 5308 + v)) (wz (T + v * 4)) (wz k) s0 (wz (dl_As L)) a0 a1 (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) s5 (wz v)
      (wz T) s3 (wz (dl_As L + 5300)) t5 (wz (dl_As L + 3008)) t6 s8 s9 s10 s11 (wz x6v) (wz x7v) (wz hlv) t4.

Lemma pq2_sel : forall (L : dlay) (T N k j q HL v n : Z) (FC DL HP DP : arr) (x7v : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= j <= HL -> HL < 573 ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv',
               ms' = MS (pqR2 L T k (sel3 FC HL DP HP j) (sel3 FC HL DP HP j) hlv' v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4' t5' t6') F (wz 0x1bbf0) fc None m (seg_rom psegs))
      (MS (pqR2 L T k j x7v HL v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bb84) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Ej Rj RHL. lay_open LAY. unfold pqR2.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zstep. br_cases K.
  -
    zs2. apply evt_done. unfold sel3. rewrite (proj2 (Z.ltb_ge j HL)) by lia. cbn [andb]. do 4 eexists. reflexivity.
  - pose proof (PQ j ltac:(lia)) as Rhj. pose proof (PQ (j + 1) ltac:(lia)) as Rhj1.
    pose proof (u32arr_read psegs m _ (av32 HP 573) j _ (wa (dl_As L + 3008 + j * 4)) HPA (av32_nth HP 573 j ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
    pose proof (u32arr_read psegs m _ (av32 HP 573) (j + 1) _ (wa (dl_As L + 3008 + (j + 1) * 4)) HPA (av32_nth HP 573 (j + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj1.
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j) ltac:(lia)) as [RDfj _].
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP (j + 1)) ltac:(lia)) as [RDfj1 _].
    replace (T + 4 * arr_get HP j) with (T + arr_get HP j * 4) in RDfj by lia. replace (T + 4 * arr_get HP (j + 1)) with (T + arr_get HP (j + 1) * 4) in RDfj1 by lia.
    pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rhj1) as Rfj1.
    zs2. replace (Z.lor j 1) with (j + 1) by (rewrite Ej, lor1_even by lia; lia).
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. zs2.
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. rewrite (zx16_small (arr_get FC (arr_get HP (j + 1)))) by lia. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j))) by lia.
    zstep. br_cases K1.
    +
      zstep. br_cases_s K2.
      *
        zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
        cbn [andb orb]. do 4 eexists. reflexivity.
      *
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP j) _ (wa (dl_As L + 5308 + arr_get HP j)) DPA (av8_nth DP 573 (arr_get HP j) ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP (j + 1)) _ (wa (dl_As L + 5308 + arr_get HP (j + 1))) DPA (av8_nth DP 573 (arr_get HP (j + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RDdj1.
        pose proof (RDP (arr_get HP j) ltac:(lia)) as Rdj. pose proof (RDP (arr_get HP (j + 1)) ltac:(lia)) as Rdj1.
        zs2. zs2. zsb. rewrite (bv8_small (arr_get DP (arr_get HP (j + 1)))) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j))) by lia.
        zs2. zstep. br_cases K3.
        -- zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
        -- zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
    +
      zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      cbn [andb orb]. do 4 eexists. reflexivity.
Qed.

Lemma pq2_cmp : forall (L : dlay) (T N k j' HL v n : Z) (FC DL HP DP : arr) (hlv : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= j' <= HL -> HL < 573 -> 0 <= v < N ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv' pcx,
               ms' = MS (pqR2 L T k (arr_get HP j') j' hlv' v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4' t5' t6') F (wz pcx) fc None m (seg_rom psegs)
               /\ ((pcx = 0x1bc24 /\ smal FC DP v (arr_get HP j') = true) \/ (pcx = 0x1bb68 /\ smal FC DP v (arr_get HP j') = false)))
      (MS (pqR2 L T k j' j' hlv v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bbf0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Rj RHL Rv. lay_open LAY. unfold pqR2.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (PQ j' Rj) as Rhj.
  pose proof (u32arr_read psegs m _ (av32 HP 573) j' _ (wa (dl_As L + 3008 + j' * 4)) HPA (av32_nth HP 573 j' ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j') ltac:(lia)) as [RDfj _].
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI v ltac:(lia)) as [RDfv _].
  replace (T + 4 * arr_get HP j') with (T + arr_get HP j' * 4) in RDfj by lia. replace (T + 4 * v) with (T + v * 4) in RDfv by lia.
  pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rv) as Rfv.
  zs2. shl_norm. zs2. zs2. zs2. rewrite (zx16_small (arr_get FC v)) by lia. zs2. shl_norm. zs2. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j'))) by lia.
  zstep. br_cases K1.
  - apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - zstep. br_cases_s K2.
    + apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
    + pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP j') _ (wa (dl_As L + 5308 + arr_get HP j')) DPA (av8_nth DP 573 (arr_get HP j') ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
      pose proof (u8arr_read psegs m _ (av8 DP 573) v _ (wa (dl_As L + 5308 + v)) DPA (av8_nth DP 573 v ltac:(lia)) ltac:(lia) eq_refl) as RDdv.
      pose proof (RDP (arr_get HP j') ltac:(lia)) as Rdj. pose proof (RDP v ltac:(lia)) as Rdv.
      zs2. zsb. rewrite (bv8_small (arr_get DP v)) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j'))) by lia.
      zstep. br_cases K3.
      * apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
        rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
      * apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. apply orb_true_r.
Qed.

Definition pq2_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists k0 x6v hlv t4 t5 t6 HP' k' m',
    ms' = MS (pqR2 L T k0 x6v k' hlv v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bc28) fc None m' (seg_rom psegs)
    /\ munch (Wpq L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL HP' HL HM DP BC OL SL MC, k')
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N) /\ 1 <= k' <= HL.

Lemma pq2_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (HP : arr) (k j q x7v : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq L) m0 T FC DL N -> mem_inv psegs m -> dlay_ok L -> munch (Wpq L) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= k -> k < j -> j <= HL -> HL < 573 -> 0 <= v < N -> fuel_ok f j HL ->
  R = pqdownheap_loop f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t v k j ->
  evt psegs (pq2_post L s t T N HL HM v n FC DL DP BC OL SL MC R ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 F fc m0)
      (MS (pqR2 L T k j x7v HL v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bb84) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM RT1 RT2 RN LHP PQ RFC RDP Ej Rk Rkj Rj RHL Rv FU ER.
  - apply fuel_ok_0 in FU. lia.
  - assert (RDTm : ct_readable [] m T FC DL N) by (eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; tauto]).
    pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.sel3_range FC HL DP HP j ltac:(lia)) as Rs3.
    rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.loop3_S_sel in ER by lia.
    eapply evt_cut; [eapply (pq2_sel L T N k j q HL v n FC DL HP DP x7v); try eassumption; lia|]. intros ms' (t4' & t5' & t6' & hlv' & ->).
    eapply evt_cut; [eapply (pq2_cmp L T N k (sel3 FC HL DP HP j) HL v n FC DL HP DP hlv'); try eassumption; lia|].
    intros ms' (t4'' & t5'' & t6'' & hlv'' & pcx & -> & [[-> SM]|[-> SM]]); rewrite SM in ER.
    +
      unfold pqR2. zs2.
      apply evt_done. unfold pq2_post, pqR2. do 9 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
      split; [exact ER|]. split; [exact LHP|]. split; [exact PQ| lia].
    +
      set (j' := sel3 FC HL DP HP j) in *.
      pose proof (PQ j' ltac:(lia)) as Rhj. lay_open LAY.
      pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
      unfold pqR2. zs2. shl_norm. zs2.
      h32_store HPA HP 573 (dl_As L + 3008) k (arr_get HP j') ltac:(reflexivity).
      zs2. zs2. shl_norm. strip32. zs2. zstep. br_cases K.
      *
        rewrite pq_out in ER by (rewrite bt_heap_len; lia).
        apply evt_done. unfold pq2_post, pqR2. do 9 eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
        split; [exact ER|]. split; [rewrite arr_len_set; exact LHP|]. split; [|lia].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
      * eapply (IH L s t T N HL HM v n FC DL DP BC OL SL MC R m0 (arr_set HP k (arr_get HP j')) j' (j' * 2) j' j');
          [exact HPA| exact DPA| exact GC| exact RDT| eassumption| assumption| exact MU| exact WM| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LHP
          | | exact RFC| exact RDP| lia| lia| lia| lia| exact RHL| exact Rv| eapply fuel_ok_S; [exact FU| lia| lia]| exact ER].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
Qed.
End Z_tr_bt4.

Module Z_tr_bt6.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition l4R (L : dlay) (T HL node dsc mc : Z) (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz HL) t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) a6 a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma pqdownheap_heap : forall s t FC DL HP HL HM DP BC OL SL MC HP' k',
  pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP 1) 1 2 = (bt_upd s t FC DL HP' HL HM DP BC OL SL MC, k') ->
  ds_heap (pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t 1) = arr_set HP' k' (arr_get HP 1).
Proof.
  intros until k'. intros E. rewrite pqdownheap_flat. change (1 * 2) with 2. rewrite E. cbn [fst snd]. rewrite bt_heap_set, bt_heap. reflexivity.
Qed.

Ltac name_mem1 id := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => is_var mm; rename mm into id end.
Notation W4 L := [(dl_As L + 3008, dl_As L + 5308)] (only parsing).

Definition l4_remove_post (L : dlay) (T N HL HM node dsc mc n : Z) (HP2 DP : arr)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a7 s5 s7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) (wz n) a7
                  (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bc34) fc None m' (seg_rom psegs)
    /\ munch (W4 L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP2 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz (HL - 1)); C4 (wz HM)]
    /\ arr_len HP2 = 573 /\ (forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP2 i < N).

Lemma l4_remove : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (W4 L) m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL < 573 ->
  evt psegs (l4_remove_post L T N HL HM node dsc mc (arr_get HP 1)
               (ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1)) DP ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (l4R L T HL node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bb2c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY RT1 RT2 RN LHP PQ RFC RDP RHL.
  pose proof (munch_refl (W4 L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (PQ HL ltac:(lia)) as Rv. pose proof (PQ 1 ltac:(lia)) as Rn1. pose proof LAY as LAY0. lay_open LAY0.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  unfold l4R. zs2. zs2. shl_norm. zs2. zs2.
  match goal with H : u32arr psegs ?mm _ (av32 HP 573) |- _ =>
    pose proof (u32arr_read psegs mm _ (av32 HP 573) HL _ (wa (dl_As L + 3008 + HL * 4)) H (av32_nth HP 573 HL ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDv;
    pose proof (u32arr_read psegs mm _ (av32 HP 573) 1 _ (wa (dl_As L + 2976 + 36)) H (av32_nth HP 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn end.
  zs2. zs2.
  h32_store HPA HP 573 (dl_As L + 3008) 1 (arr_get HP HL) ltac:(reflexivity).
  zs2. zstep. br_cases K.
  -
    set (HP1 := arr_set HP 1 (arr_get HP HL)) in *.
    assert (E1 : arr_get HP1 1 = arr_get HP HL) by (subst HP1; apply arr_get_set_same; lia).
    assert (EH : ds_heap (pqdownheap (bt_upd s t FC DL HP1 (HL - 1) HM DP BC OL SL MC) t 1) = arr_set HP1 1 (arr_get HP HL)).
    { rewrite <- E1. apply pqdownheap_heap. apply pq_out. rewrite bt_heap_len. lia. }
    zs2. zs2.
    h32_store HPA HP1 573 (dl_As L + 3008) 1 (arr_get HP HL) ltac:(reflexivity).
    apply evt_done. unfold l4_remove_post. rewrite EH. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [subst HP1; rewrite !arr_len_set; exact LHP|].
    intros i Hi. replace i with 1 by lia. rewrite arr_get_set_same by (subst HP1; rewrite arr_len_set; lia). exact Rv.
  -
    set (HP1 := arr_set HP 1 (arr_get HP HL)) in *.
    assert (E1 : arr_get HP1 1 = arr_get HP HL) by (subst HP1; apply arr_get_set_same; lia).
    assert (PQ1 : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP1 i < N).
    { intros i Hi. subst HP1. destruct (Z.eq_dec 1 i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply PQ; lia]. }
    zs2. zs2. shl_norm. zs2. zs2. zs2. zs2. name_mem1 m2.
    call (pq2_loop 32 L s t T N (HL - 1) HM (arr_get HP HL) 0 FC DL DP BC OL SL MC
            (pqdownheap_loop 32 (bt_upd s t FC DL HP1 (HL - 1) HM DP BC OL SL MC) t (arr_get HP HL) 1 2) m2 HP1 1 2 1 1).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ subst HP1. rewrite arr_len_set. exact LHP. } 1:{ exact PQ1. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rv. }
    1:{ unfold fuel_ok. change (2 ^ Z.of_nat 32) with 4294967296. lia. } 1:{ reflexivity. }
    match goal with E : pqdownheap_loop _ _ _ _ _ _ = (bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, ?kk), H : u32arr psegs ?mm _ (av32 ?hp 573), HD : u8arr psegs ?mm _ (av8 DP 573),
                     HG : rw_cells psegs ?mm (dl_As L + 5300) _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (EH : ds_heap (pqdownheap (bt_upd s t FC DL HP1 (HL - 1) HM DP BC OL SL MC) t 1) = arr_set hp kk (arr_get HP HL))
        by (rewrite <- E1; apply pqdownheap_heap; rewrite E1; exact E);
      rename H into HPB; rename HD into DPB; rename HG into GCB; pose proof (av32_zlength hp 573 ltac:(lia)) as L32b;
      unfold pqR2; zs2; shl_norm; zs2;
      h32_store HPB hp 573 (dl_As L + 3008) kk (arr_get HP HL) ltac:(reflexivity);
      apply evt_done; unfold l4_remove_post; rewrite EH; do 11 eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HPB|]; split; [exact DPB|]; split; [exact GCB|];
      split; [rewrite arr_len_set; exact HL'|];
      intros i Hi; destruct (Z.eq_dec kk i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply HQ; exact Hi] end.
Qed.
End Z_tr_bt6.

Module Z_tr_bt7.
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
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma le2_add_sx16_2 : forall a b, le2 (wz (bv_unsigned (sx16 (wz b)) + bv_unsigned (sx16 (wz a)))) = le2 (wz (wrap16 (a + b))).
Proof.
  intros a b. apply le2_wz_mod. rewrite lo16_unsigned_wz, wrap16_mod, lo16_idem.
  rewrite Z.add_mod by lia. rewrite !lo16_sx16, !lo16_unsigned_wz. rewrite <- Z.add_mod by lia. f_equal. lia.
Qed.

Notation W5 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).

Definition l4_node_post (L : dlay) (T N HL HM node dsc mc : Z) (FC' DL' HP3 DP' : arr)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s5 s7 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) (wz (T + node * 4)) (wz (dl_As L + 5308 + node))
                  (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 (wz HL) t4 t5 t6) F (wz 0x1bcc4) fc None m' (seg_rom psegs)
    /\ munch (W5 L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP3 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz (HM - 2))].

Ltac l4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC :=
  zs2; zs2;
  match goal with |- context [wz (?d + 1)] => pb_store DPA DP 573 (dl_As L + 5308) node (wrap8 (d + 1)) ltac:(apply lo8_wz_wrap8; lia) end;
  ct_store_dl ARR (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_))) DL N T m_ (wrap16 node) ltac:(rewrite (wrap16_id node) by lia; reflexivity);
  ct_store_dl ARR (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_))) (arr_set DL m_ (wrap16 node)) N T n (wrap16 node) ltac:(rewrite (wrap16_id node) by lia; reflexivity);
  zs2;
  h32_store HPA (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 573 (dl_As L + 3008) 1 node ltac:(reflexivity);
  apply evt_done; unfold l4_node_post; do 9 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ARR|]; split; [exact HPA|]; split; [exact DPA| exact GC].

Lemma l4_node : forall (L : dlay) (T N HL HM node dsc mc n m_ : Z) (FC DL HP2 DP : arr)
    (ra sp gp tp t0 t1 t2 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP2 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP2 = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  m_ = arr_get HP2 1 -> 0 <= n < N -> 0 <= m_ < N -> 0 <= node < N -> 1 <= HL < 573 -> 3 <= HM <= 573 ->
  evt psegs (l4_node_post L T N HL HM node dsc mc (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)))
               (arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node)) (arr_set (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 1 node)
               (arr_set DP node (wrap8 (dmax DP n m_ + 1))) ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) (wz n) a7
               (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bc34) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA GC MI LAY RT1 RT2 RN LFC LDL LHP LDP RFC RDP Em Rn Rm Rnode RHL RHM.
  pose proof (munch_refl (W5 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP2 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (u32arr_read psegs m _ (av32 HP2 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP2 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDm. rewrite <- Em in RDm.
  zs2. zs2. shl_norm. zs2. zs2. zs2. shl_norm. zs2. zs2.
  h32_store HPA HP2 573 (dl_As L + 3008) (HM - 1) n ltac:(reflexivity).
  zs2. zs2. zs2. shl_norm. zs2. zs2. zs2. shl_norm. zs2. zs2.
  h32_store HPA (arr_set HP2 (HM - 1) n) 573 (dl_As L + 3008) (HM - 2) m_ ltac:(reflexivity).
  match goal with H : u8arr psegs ?mm T _ |- _ =>
    pose proof (u16arr_read psegs mm T (avct FC DL N) (2 * n) _ (wa (T + n * 4)) H (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDfn;
    pose proof (u16arr_read psegs mm T (avct FC DL N) (2 * m_) _ (wa (T + m_ * 4)) H (avct_nth_fc FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDfm end.
  zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2.
  ct_store_fc ARR FC DL N T node (wrap16 (arr_get FC n + arr_get FC m_)) ltac:(apply le2_add_sx16_2).
  pose proof (RDP n ltac:(lia)) as Rdn. pose proof (RDP m_ ltac:(lia)) as Rdm.
  match goal with H : u8arr psegs ?mm (dl_As L + 5308) _ |- _ =>
    pose proof (u8arr_read psegs mm _ (av8 DP 573) n _ (wa (dl_As L + 5308 + n)) H (av8_nth DP 573 n ltac:(lia)) ltac:(lia) eq_refl) as RDdn;
    pose proof (u8arr_read psegs mm _ (av8 DP 573) m_ _ (wa (dl_As L + 5308 + m_)) H (av8_nth DP 573 m_ ltac:(lia)) ltac:(lia) eq_refl) as RDdm end.
  zsb. rewrite (bv8_small (arr_get DP n)) by lia. zsb. rewrite (bv8_small (arr_get DP m_)) by lia.
  zstep. br_cases K.
  -
    assert (ED : dmax DP n m_ = arr_get DP n) by (unfold dmax; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity). rewrite ED.
    l4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC.
  - assert (ED : dmax DP n m_ = arr_get DP m_) by (unfold dmax; destruct (Z.leb_spec (arr_get DP m_) (arr_get DP n)); lia). rewrite ED.
    zs2. l4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC.
Qed.
End Z_tr_bt7.

Module Z_tr_bt5.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition pqR3 (L : dlay) (T k x6v x7v hlv v n : Z) (ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz k) (wz x6v) (wz x7v) s0 (wz (dl_As L)) (wz v) a1 (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) (wz (T + v * 4)) (wz (dl_As L + 5308 + v))
      (wz T) s3 (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 (wz hlv) t4 t5 t6.

Lemma pq3_sel : forall (L : dlay) (T N k j q HL v n : Z) (FC DL HP DP : arr) (x7v : Z)
    (ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= j <= HL -> HL < 573 ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv',
               ms' = MS (pqR3 L T k (sel3 FC HL DP HP j) (sel3 FC HL DP HP j) hlv' v n ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4' t5' t6') F (wz 0x1bd5c) fc None m (seg_rom psegs))
      (MS (pqR3 L T k j x7v HL v n ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bcf0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Ej Rj RHL. lay_open LAY. unfold pqR3.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zstep. br_cases K.
  -
    zs2. apply evt_done. unfold sel3. rewrite (proj2 (Z.ltb_ge j HL)) by lia. cbn [andb]. do 4 eexists. reflexivity.
  - pose proof (PQ j ltac:(lia)) as Rhj. pose proof (PQ (j + 1) ltac:(lia)) as Rhj1.
    pose proof (u32arr_read psegs m _ (av32 HP 573) j _ (wa (dl_As L + 3008 + j * 4)) HPA (av32_nth HP 573 j ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
    pose proof (u32arr_read psegs m _ (av32 HP 573) (j + 1) _ (wa (dl_As L + 3008 + (j + 1) * 4)) HPA (av32_nth HP 573 (j + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj1.
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j) ltac:(lia)) as [RDfj _].
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP (j + 1)) ltac:(lia)) as [RDfj1 _].
    replace (T + 4 * arr_get HP j) with (T + arr_get HP j * 4) in RDfj by lia. replace (T + 4 * arr_get HP (j + 1)) with (T + arr_get HP (j + 1) * 4) in RDfj1 by lia.
    pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rhj1) as Rfj1.
    zs2. replace (Z.lor j 1) with (j + 1) by (rewrite Ej, lor1_even by lia; lia).
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. zs2.
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. rewrite (zx16_small (arr_get FC (arr_get HP (j + 1)))) by lia. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j))) by lia.
    zstep. br_cases K1.
    +
      zstep. br_cases_s K2.
      *
        zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
        cbn [andb orb]. do 4 eexists. reflexivity.
      *
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP j) _ (wa (dl_As L + 5308 + arr_get HP j)) DPA (av8_nth DP 573 (arr_get HP j) ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP (j + 1)) _ (wa (dl_As L + 5308 + arr_get HP (j + 1))) DPA (av8_nth DP 573 (arr_get HP (j + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RDdj1.
        pose proof (RDP (arr_get HP j) ltac:(lia)) as Rdj. pose proof (RDP (arr_get HP (j + 1)) ltac:(lia)) as Rdj1.
        zs2. zs2. zsb. rewrite (bv8_small (arr_get DP (arr_get HP (j + 1)))) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j))) by lia.
        zs2. zstep. br_cases K3.
        -- zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
        -- zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
    +
      zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      cbn [andb orb]. do 4 eexists. reflexivity.
Qed.

Lemma pq3_cmp : forall (L : dlay) (T N k j' HL v n : Z) (FC DL HP DP : arr) (hlv : Z)
    (ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= j' <= HL -> HL < 573 -> 0 <= v < N ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv' pcx,
               ms' = MS (pqR3 L T k (arr_get HP j') j' hlv' v n ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4' t5' t6') F (wz pcx) fc None m (seg_rom psegs)
               /\ ((pcx = 0x1bd90 /\ smal FC DP v (arr_get HP j') = true) \/ (pcx = 0x1bcd4 /\ smal FC DP v (arr_get HP j') = false)))
      (MS (pqR3 L T k j' j' hlv v n ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bd5c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Rj RHL Rv. lay_open LAY. unfold pqR3.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (PQ j' Rj) as Rhj.
  pose proof (u32arr_read psegs m _ (av32 HP 573) j' _ (wa (dl_As L + 3008 + j' * 4)) HPA (av32_nth HP 573 j' ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j') ltac:(lia)) as [RDfj _].
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI v ltac:(lia)) as [RDfv _].
  replace (T + 4 * arr_get HP j') with (T + arr_get HP j' * 4) in RDfj by lia. replace (T + 4 * v) with (T + v * 4) in RDfv by lia.
  pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rv) as Rfv.
  zs2. shl_norm. zs2. zs2. zs2. rewrite (zx16_small (arr_get FC v)) by lia. zs2. shl_norm. zs2. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j'))) by lia.
  zstep. br_cases K1.
  - apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - zstep. br_cases_s K2.
    + apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
    + pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP j') _ (wa (dl_As L + 5308 + arr_get HP j')) DPA (av8_nth DP 573 (arr_get HP j') ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
      pose proof (u8arr_read psegs m _ (av8 DP 573) v _ (wa (dl_As L + 5308 + v)) DPA (av8_nth DP 573 v ltac:(lia)) ltac:(lia) eq_refl) as RDdv.
      pose proof (RDP (arr_get HP j') ltac:(lia)) as Rdj. pose proof (RDP v ltac:(lia)) as Rdv.
      zs2. zsb. rewrite (bv8_small (arr_get DP v)) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j'))) by lia.
      zstep. br_cases K3.
      * apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
        rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
      * apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. apply orb_true_r.
Qed.

Definition pq3_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists k0 x6v hlv t4 t5 t6 HP' k' m',
    ms' = MS (pqR3 L T k0 x6v k' hlv v n ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bb14) fc None m' (seg_rom psegs)
    /\ munch (Wpq L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL HP' HL HM DP BC OL SL MC, k')
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N) /\ 1 <= k' <= HL.

Lemma pq3_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (HP : arr) (k j q x7v : Z)
    (ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq L) m0 T FC DL N -> mem_inv psegs m -> dlay_ok L -> munch (Wpq L) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= k -> k < j -> j <= HL -> HL < 573 -> 0 <= v < N -> fuel_ok f j HL ->
  R = pqdownheap_loop f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t v k j ->
  evt psegs (pq3_post L s t T N HL HM v n FC DL DP BC OL SL MC R ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 F fc m0)
      (MS (pqR3 L T k j x7v HL v n ra sp gp tp s0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bcf0) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM RT1 RT2 RN LHP PQ RFC RDP Ej Rk Rkj Rj RHL Rv FU ER.
  - apply fuel_ok_0 in FU. lia.
  - assert (RDTm : ct_readable [] m T FC DL N) by (eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; tauto]).
    pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.sel3_range FC HL DP HP j ltac:(lia)) as Rs3.
    rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.loop3_S_sel in ER by lia.
    eapply evt_cut; [eapply (pq3_sel L T N k j q HL v n FC DL HP DP x7v); try eassumption; lia|]. intros ms' (t4' & t5' & t6' & hlv' & ->).
    eapply evt_cut; [eapply (pq3_cmp L T N k (sel3 FC HL DP HP j) HL v n FC DL HP DP hlv'); try eassumption; lia|].
    intros ms' (t4'' & t5'' & t6'' & hlv'' & pcx & -> & [[-> SM]|[-> SM]]); rewrite SM in ER.
    +
      unfold pqR3. zs2. zs2.
      apply evt_done. unfold pq3_post, pqR3. do 9 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
      split; [exact ER|]. split; [exact LHP|]. split; [exact PQ| lia].
    +
      set (j' := sel3 FC HL DP HP j) in *.
      pose proof (PQ j' ltac:(lia)) as Rhj. lay_open LAY.
      pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
      unfold pqR3. zs2. shl_norm. zs2.
      h32_store HPA HP 573 (dl_As L + 3008) k (arr_get HP j') ltac:(reflexivity).
      zs2. zs2. shl_norm. strip32. zs2. zstep. br_cases K.
      *
        rewrite pq_out in ER by (rewrite bt_heap_len; lia).
        apply evt_done. unfold pq3_post, pqR3. do 9 eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
        split; [exact ER|]. split; [rewrite arr_len_set; exact LHP|]. split; [|lia].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
      * eapply (IH L s t T N HL HM v n FC DL DP BC OL SL MC R m0 (arr_set HP k (arr_get HP j')) j' (j' * 2) j' j');
          [exact HPA| exact DPA| exact GC| exact RDT| eassumption| assumption| exact MU| exact WM| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LHP
          | | exact RFC| exact RDP| lia| lia| lia| lia| exact RHL| exact Rv| eapply fuel_ok_S; [exact FU| lia| lia]| exact ER].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
Qed.
End Z_tr_bt5.

Module Z_tr_bt8.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt5 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition l4_down_post (L : dlay) (T N HL HM node1 dsc mc : Z) (HPf DP : arr)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a6 a7 s5 s7 t3 t4 t5 t6 pcx m',
    ms' = MS (l4R L T HL node1 dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (W4 L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HPf 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ arr_len HPf = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HPf i < N)
    /\ ((pcx = 0x1bb2c /\ 2 <= HL) \/ (pcx = 0x1bd98 /\ HL < 2)).

Lemma l4_down : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (FC DL HP3 DP BC : arr) (OL SL MC : Z)
    (ra sp gp tp t0 t1 t2 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP3 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (W4 L) m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP3 = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP3 i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= HL < 573 -> 0 <= node < N -> arr_get HP3 1 = node -> node + 1 < 2^31 ->
  evt psegs (l4_down_post L T N HL HM (node + 1) dsc mc
               (ds_heap (pqdownheap (bt_upd s t FC DL HP3 HL HM DP BC OL SL MC) t 1)) DP ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) (wz (T + node * 4)) (wz (dl_As L + 5308 + node))
               (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 (wz HL) t4 t5 t6) F (wz 0x1bcc4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY RT1 RT2 RN LHP PQ RFC RDP RHL Rnode E1 Rn1.
  pose proof (munch_refl (W4 L) m) as MU. pose proof (wmono_refl psegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  pose proof (av32_zlength HP3 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zstep. br_cases K.
  -
    assert (EH : ds_heap (pqdownheap (bt_upd s t FC DL HP3 HL HM DP BC OL SL MC) t 1) = arr_set HP3 1 node).
    { rewrite <- E1. apply pqdownheap_heap. apply pq_out. rewrite bt_heap_len. lia. }
    zs2. zs2. zs2.
    h32_store HPA HP3 573 (dl_As L + 3008) 1 node ltac:(reflexivity).
    zs2. zs2. zstep. br_cases K2; [|exfalso; lia].
    apply evt_done. unfold l4_down_post, l4R. rewrite EH. do 12 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [rewrite arr_len_set; exact LHP|]. split; [|right; split; [reflexivity| lia]].
    intros i Hi. replace i with 1 by lia. rewrite arr_get_set_same by lia. exact Rnode.
  -
    zs2. zs2. zs2.
    assert (Et2 : t2 = wz (bv_unsigned t2)) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite Et2. clear Et2.
    call (pq3_loop 32 L s t T N HL HM node 0 FC DL DP BC OL SL MC
            (pqdownheap_loop 32 (bt_upd s t FC DL HP3 HL HM DP BC OL SL MC) t node 1 2) m HP3 1 2 1).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. }
    1:{ eapply ct_readable_rebase; [exact RDT| apply munch_refl| apply wmono_refl| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rnode. }
    1:{ unfold fuel_ok. change (2 ^ Z.of_nat 32) with 4294967296. lia. } 1:{ reflexivity. }
    match goal with E : pqdownheap_loop _ _ _ _ _ _ = (bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, ?kk), H : u32arr psegs ?mm _ (av32 ?hp 573), HD : u8arr psegs ?mm _ (av8 DP 573),
                     HG : rw_cells psegs ?mm (dl_As L + 5300) _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (EH : ds_heap (pqdownheap (bt_upd s t FC DL HP3 HL HM DP BC OL SL MC) t 1) = arr_set hp kk node)
        by (rewrite <- E1; apply pqdownheap_heap; rewrite E1; exact E);
      rename H into HPB; rename HD into DPB; rename HG into GCB; pose proof (av32_zlength hp 573 ltac:(lia)) as L32b;
      unfold pqR3; zs2; shl_norm; zs2;
      h32_store HPB hp 573 (dl_As L + 3008) kk node ltac:(reflexivity);
      zs2; zs2; zstep; br_cases K2; [exfalso; lia|];
      apply evt_done; unfold l4_down_post, l4R; rewrite EH; do 12 eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HPB|]; split; [exact DPB|]; split; [exact GCB|];
      split; [rewrite arr_len_set; exact HL'|]; split; [|left; split; [reflexivity| lia]];
      intros i Hi; destruct (Z.eq_dec kk i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rnode| rewrite arr_get_set_other by exact NE; apply HQ; exact Hi] end.
Qed.
End Z_tr_bt8.

Module Z_tr_bt10.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt7 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt8 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Ltac name_term X EX t :=
  let H := fresh in
  assert (H : exists X0, X0 = t) by (eexists; reflexivity);
  destruct H as [X EX]; rewrite <- ?EX in *.

Definition l4_iter_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a6 a7 s5 s7 t3 t4 t5 t6 FC' DL' HP' DP' pcx m',
    ms' = MS (l4R L T (HL - 1) (node + 1) dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (W5 L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz (HL - 1)); C4 (wz (HM - 2))]
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573
    /\ (forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP' i < N) /\ (forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256)
    /\ ((pcx = 0x1bb2c /\ 2 <= HL - 1 /\ R = build_tree_loop4 f (bt_upd s t FC' DL' HP' (HL - 1) (HM - 2) DP' BC OL SL MC) t (node + 1))
        \/ (pcx = 0x1bd98 /\ HL - 1 < 2 /\ R = bt_upd s t FC' DL' HP' (HL - 1) (HM - 2) DP' BC OL SL MC)).

Lemma l4_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL < 573 -> 0 <= node < N -> 3 <= HM <= 573 ->
  R = build_tree_loop4 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t node ->
  evt psegs (l4_iter_post L s t T N HL HM node dsc mc BC OL SL MC f R ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (l4R L T HL node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bb2c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA GC MI LAY RT1 RT2 RN LFC LDL LHP LDP PQ RFC RDP RHL Rnode RHM ER.
  pose proof (munch_refl (W5 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (dlay_ranges _ LAY) as (Rs & _).
  assert (RDT : ct_readable (W4 L) m T FC DL N) by (eapply ct_readable_rw; [exact ARR| lia| lia| cbn [disjoint_from]; lia]).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT.
  call (l4_remove L s t T N HL HM node dsc mc FC DL HP DP BC OL SL MC).
  1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact RDT. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
  1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ exact RHL. }
  clear RDT.
  match goal with H : u32arr psegs _ _ (av32 ?hp2 573) |- _ => name_term HP2 EHP2 hp2 end.
  pose proof (PQ 1 ltac:(lia)) as Rn.
  match goal with HQ : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP2 i < N |- _ => pose proof (HQ 1 ltac:(lia)) as Rm; rename HQ into PQ2 end.
  match goal with H : u32arr psegs ?mm _ (av32 HP2 573), HD : u8arr psegs ?mm (dl_As L + 5308) _, HG : rw_cells psegs ?mm (dl_As L + 5300) _,
                   HLn : arr_len HP2 = 573 |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    rename HLn into LHP2;
    call (l4_node L T N (HL - 1) HM node dsc mc (arr_get HP 1) (arr_get HP2 1) FC DL HP2 DP);
    [exact ARR| exact H| exact HD| exact HG| eassumption| exact LAY| exact RT1| exact RT2| exact RN| exact LFC| exact LDL| exact LHP2| exact LDP| exact RFC| exact RDP
    | reflexivity| exact Rn| exact Rm| exact Rnode| lia| exact RHM|] end.
  match goal with H : u8arr psegs _ T (u16s (avct ?fc' ?dl' N)) |- _ => name_term FC' EFC fc'; name_term DL' EDL dl'; rename H into ARR' end.
  match goal with H : u32arr psegs _ _ (av32 ?hp3 573) |- _ => name_term HP3 EHP3 hp3; rename H into HPA3 end.
  match goal with H : u8arr psegs _ (dl_As L + 5308) (av8 ?dp' 573) |- _ => name_term DP' EDP dp'; rename H into DPA' end.
  assert (LFC' : arr_len FC' = N) by (rewrite EFC, arr_len_set; exact LFC).
  assert (LDL' : arr_len DL' = N) by (rewrite EDL, !arr_len_set; exact LDL).
  assert (LHP3 : arr_len HP3 = 573) by (rewrite EHP3, !arr_len_set; exact LHP2).
  assert (LDP' : arr_len DP' = 573) by (rewrite EDP, arr_len_set; exact LDP).
  assert (RFC' : forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536).
  { intros i Hi. rewrite EFC. destruct (Z.eq_dec node i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RFC; exact Hi]. }
  assert (RDP' : forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256).
  { intros i Hi. rewrite EDP. destruct (Z.eq_dec node i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply Z_tr_cb3.wrap8_range| rewrite arr_get_set_other by exact NE; apply RDP; exact Hi]. }
  assert (E31 : arr_get HP3 1 = node) by (rewrite EHP3; apply arr_get_set_same; rewrite !arr_len_set; lia).
  assert (PQ3 : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP3 i < N).
  { intros i Hi. rewrite EHP3. destruct (Z.eq_dec 1 i) as [<-|NE1]; [rewrite arr_get_set_same by (rewrite !arr_len_set; lia); exact Rnode|].
    rewrite arr_get_set_other by exact NE1. destruct (Z.eq_dec (HM - 2) i) as [<-|NE2]; [rewrite arr_get_set_same by (rewrite !arr_len_set; lia); exact Rm|].
    rewrite arr_get_set_other by exact NE2. destruct (Z.eq_dec (HM - 1) i) as [<-|NE3]; [rewrite arr_get_set_same by lia; exact Rn|].
    rewrite arr_get_set_other by exact NE3. apply PQ2. exact Hi. }
  pose proof (avct_zlength FC' DL' N ltac:(lia)) as LCT'.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RDT' : ct_readable (W4 L) mm T FC' DL' N) by (eapply ct_readable_rw; [exact ARR'| lia| lia| cbn [disjoint_from]; lia]) end.
  call (l4_down L s t T N (HL - 1) (HM - 2) node dsc mc FC' DL' HP3 DP' BC OL SL MC).
  1:{ exact HPA3. } 1:{ exact DPA'. } 1:{ eassumption. } 1:{ exact RDT'. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP3. }
  1:{ exact PQ3. } 1:{ exact RFC'. } 1:{ exact RDP'. } 1:{ lia. } 1:{ exact Rnode. } 1:{ exact E31. } 1:{ lia. }
  match goal with H : u32arr psegs _ _ (av32 ?hpf 573) |- _ => name_term HPf EHPf hpf; rename H into HPAf end.
  pose proof (l4_model s t BC OL SL MC FC DL HP HL HM DP node f R HP2 (arr_get HP2 1) FC' DL' HP3 DP' HPf ER EHP2 eq_refl EFC EDL EHP3 EDP EHPf) as EM.
  apply evt_done. unfold l4_iter_post. do 10 eexists. exists FC', DL', HPf, DP'. do 2 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR'|]. split; [exact HPAf|]. split; [eassumption|]. split; [eassumption|].
  split; [exact LFC'|]. split; [exact LDL'|]. split; [eassumption|]. split; [exact LDP'|]. split; [eassumption|]. split; [exact RFC'|]. split; [exact RDP'|].
  match goal with H : _ /\ _ \/ _ /\ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - left. split; [reflexivity|]. split; [exact K|]. rewrite (proj2 (Z.leb_le 2 (HL - 1)) K) in EM. exact EM.
  - right. split; [reflexivity|]. split; [exact K|]. rewrite (proj2 (Z.leb_gt 2 (HL - 1)) K) in EM. exact EM.
Qed.

Definition bt_loop4_post (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc mc : Z) (BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a6 a7 s5 s7 t3 t4 t5 t6 FC' DL' HP' DP' HM' node' m',
    ms' = MS (l4R L T 1 node' dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bd98) fc None m' (seg_rom psegs)
    /\ munch (W5 L T N) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz HM')]
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573
    /\ 0 <= arr_get HP' 1 < N /\ (forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256)
    /\ 1 <= HM' <= 571
    /\ R = bt_upd s t FC' DL' HP' 1 HM' DP' BC OL SL MC.

Lemma bt_loop4 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> mem_inv psegs m -> dlay_ok L -> munch (W5 L T N) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL -> HL <= Z.of_nat f -> 0 <= node -> node + HL <= N -> 2 * HL <= HM + 1 -> HM <= 573 ->
  R = build_tree_loop4 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t node ->
  evt psegs (bt_loop4_post L s t T N dsc mc BC OL SL MC R ra sp gp tp s8 s9 s10 s11 F fc m0)
      (MS (l4R L T HL node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bb2c) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA DPA GC MI LAY MU WM RT1 RT2 RN LFC LDL LHP LDP PQ RFC RDP RHL Hf Rnode RC RK RHM ER.
  { exfalso. lia. }
  call (l4_iter L s t T N HL HM node dsc mc FC DL HP DP BC OL SL MC f R).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
  1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ER. }
  match goal with H : _ \/ _ |- _ => destruct H as [(-> & K & ER')|(-> & K & ER')] end.
  - match goal with HT : u8arr psegs ?mm T (u16s (avct ?fc' ?dl' N)), HA : u32arr psegs ?mm _ (av32 ?hp' 573), HD : u8arr psegs ?mm (dl_As L + 5308) (av8 ?dp' 573),
                     HG : rw_cells psegs ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N (HL - 1) (HM - 2) (node + 1) dsc mc fc' dl' hp' dp' BC OL SL MC R m0);
        [exact HT| exact HA| exact HD| exact HG| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact RN| assumption| assumption| assumption| assumption
        | assumption| assumption| assumption| exact K| lia| lia| lia| lia| lia| exact ER'] end.
  - replace (HL - 1) with 1 in * by lia.
    apply evt_done. unfold bt_loop4_post. do 10 eexists.
    match goal with HT : u8arr psegs ?mm T (u16s (avct ?fc' ?dl' N)), HA : u32arr psegs ?mm _ (av32 ?hp' 573), HD : u8arr psegs ?mm (dl_As L + 5308) (av8 ?dp' 573),
                     HQ : forall i, 1 <= i <= 1 -> _ |- _ =>
      exists fc', dl', hp', dp', (HM - 2), (node + 1); eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HA|]; split; [exact HD|]; split; [eassumption|];
      split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [apply HQ; lia|]; split; [assumption|]; split; [assumption|];
      split; [lia| exact ER'] end.
Qed.
End Z_tr_bt10.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt10 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition xbits_view (t : tree_id) (xp : Z) : Prop :=
  forall mm n, mem_inv psegs mm -> sd_extra_base t <= n < sd_elems t ->
    ov_read_bytes psegs mm (wa (xp + (n - sd_extra_base t) * 4)) 4 = Some (le4 (wz (arr_get (sd_extra_bits t) (n - sd_extra_base t))))
    /\ 0 <= arr_get (sd_extra_bits t) (n - sd_extra_base t) < 16.
Definition stree_view_n (t : tree_id) (stp : Z) : Prop :=
  (stp = 0 /\ stree_has t = false)
  \/ (0 < stp < 2^32 /\ stree_has t = true
      /\ forall mm n, mem_inv psegs mm -> 0 <= n < sd_elems t ->
           ov_read_bytes psegs mm (wa (stp + n * 4 + 2)) 2 = Some (le2 (wz (stree_Len t n))) /\ 0 <= stree_Len t n < 16).

Definition gbR (L : dlay) (T h ovf base mc ML stp xp : Z) (ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz ovf) (wz 2976) (wz 4294967295) (wz (h + 1)) (wz (dl_As L + 3008 + 4 * h)) (wz 573) a6 a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) (wz base) s6 (wz T) (wz mc) (wz ML) (wz stp) (wz xp) t3 t4 t5 t6.

Definition gb1_head_post (L : dlay) (T N h ovf base mc ML stp xp n dlen bits : Z) (FC DL' : arr)
    (ra sp gp tp s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (gbR L T h ovf base mc ML stp xp ra sp gp tp (wz (T + n * 4)) (wz bits) (wz n) (wz dlen) (wz (n * 4)) s6 t3 t4 t5 t6) F (wz 0x1be80) fc None m' (seg_rom psegs)
    /\ munch [(T, T + 4 * N)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)).

Lemma gb1_head : forall (L : dlay) (T N h ovf base mc ML stp xp n dlen bits : Z) (FC DL HP : arr)
    (ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  0 <= h < 573 -> n = arr_get HP h -> 0 <= n < N -> 0 <= arr_get DL n < N -> dlen = arr_get DL (arr_get DL n) -> 0 <= dlen < 65536 -> 1 <= ML <= 15 ->
  bits = (if ML <=? dlen then ML else dlen + 1) ->
  evt psegs (gb1_head_post L T N h ovf base mc ML stp xp n dlen bits FC (arr_set DL n (wrap16 bits)) ra sp gp tp s6 t3 t4 t5 t6 F fc m)
      (MS (gbR L T h ovf base mc ML stp xp ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz 0x1be54) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA MI LAY RT1 RT2 RN LFC LDL LHP Rh En Rn Rd Ed Rdl RML Eb.
  pose proof (munch_refl [(T, T + 4 * N)] m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  pose proof (u32arr_read psegs m _ (av32 HP 573) h _ (wa (dl_As L + 3008 + 4 * h)) HPA (av32_nth HP 573 h ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn. rewrite <- En in RDn.
  pose proof (u16arr_read psegs m T (avct FC DL N) (2 * n + 1) _ (wa (T + n * 4 + 2)) ARR (avct_nth_dl FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDd.
  pose proof (u16arr_read psegs m T (avct FC DL N) (2 * arr_get DL n + 1) _ (wa (T + arr_get DL n * 4 + 2)) ARR (avct_nth_dl FC DL N (arr_get DL n) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
  rewrite <- Ed in RDl.
  unfold gbR. zs2. zs2. shl_norm. zs2. zs2.
  rewrite zx16_small by lia. zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zs2.
  zstep. br_cases K.
  - rewrite (proj2 (Z.leb_le ML dlen) K) in Eb. subst bits.
    ct_store_dl ARR FC DL N T n (wrap16 ML) ltac:(rewrite (wrap16_id ML) by lia; reflexivity).
    apply evt_done. unfold gb1_head_post, gbR. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
  - rewrite (proj2 (Z.leb_gt ML dlen)) in Eb by lia. subst bits.
    zs2.
    ct_store_dl ARR FC DL N T n (wrap16 (dlen + 1)) ltac:(rewrite (wrap16_id (dlen + 1)) by lia; reflexivity).
    apply evt_done. unfold gb1_head_post, gbR. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
Qed.

Ltac a16_store ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok psegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av16_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "L16" in pose proof (av16_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNB" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Definition gb1_cnt_post (L : dlay) (T h ovf base mc ML stp xp n dlen bits xb : Z) (BC' : arr)
    (ra sp gp tp s6 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t3 t4 m',
    ms' = MS (gbR L T h ovf base mc ML stp xp ra sp gp tp (wz (T + n * 4)) (wz bits) (wz xb) (wz dlen) (wz (n * 4)) s6 t3 t4 t5 t6) F (wz 0x1beb4) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 2976, dl_As L + 3008)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16)).

Lemma gb1_cnt : forall (L : dlay) (t : tree_id) (T h ovf mc stp xp n dlen bits : Z) (BC : arr)
    (ra sp gp tp s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv psegs m -> dlay_ok L -> arr_len BC = 16 ->
  xbits_view t xp -> 0 <= n -> n <= mc -> mc < sd_elems t -> 1 <= bits <= 15 -> 0 <= sd_extra_base t < 2^31 -> sd_elems t < 2^31 ->
  evt psegs (gb1_cnt_post L T h ovf (sd_extra_base t) mc (sd_max_length t) stp xp n dlen bits (xbits t n) (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
               ra sp gp tp s6 t5 t6 F fc m)
      (MS (gbR L T h ovf (sd_extra_base t) mc (sd_max_length t) stp xp ra sp gp tp (wz (T + n * 4)) (wz bits) (wz n) (wz dlen) (wz (n * 4)) s6 t3 t4 t5 t6)
          F (wz 0x1be84) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros BLC MI LAY LBC XV Rn0 Rn Rmc Rb Rbase RE.
  pose proof (munch_refl [(dl_As L + 2976, dl_As L + 3008)] m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY.
  pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (u16arr_read psegs m _ (av16 BC 16) bits _ (wa (dl_As L + 2976 + bits * 2)) BLC (av16_nth BC 16 bits ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
  unfold gbR. zs2. shl_norm. zs2. zs2. zs2.
  a16_store BLC BC 16 (dl_As L + 2976) bits (wrap16 (arr_get BC bits + 1)) ltac:(apply le2_add_sx16).
  zstep. br_cases K.
  - assert (EX : xbits t n = arr_get (sd_extra_bits t) (n - sd_extra_base t)) by (unfold xbits; rewrite (proj2 (Z.leb_le _ _) K); reflexivity).
    match goal with MI' : mem_inv psegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (XV mm n MI' ltac:(lia)) as [RDx Rx] end.
    rewrite <- EX in RDx, Rx.
    zs2. zs2. shl_norm. zs2. zs2.
    apply evt_done. unfold gb1_cnt_post, gbR. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact BLC].
  - assert (EX : xbits t n = 0) by (unfold xbits; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity). rewrite EX.
    zs2. zs2.
    apply evt_done. unfold gb1_cnt_post, gbR. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact BLC].
Qed.

Lemma wz_wrap64 : forall x, wz (wrap64 x) = wz x.
Proof. intros. apply Z_to_bv_eqm. rewrite wrap64_mod, Z.mod_mod by lia. reflexivity. Qed.

Notation Wgl L := [(dl_As L + 5881, dl_As L + 5968)] (only parsing).

Definition gb1_len_post (L : dlay) (s : deflate_state) (T h ovf base mc ML stp xp dlen : Z) (OL' SL' : Z)
    (ra sp gp tp s6 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a7 t3 h0 h1 h2 h3 h4 m',
    ms' = MS (gbR L T h ovf base mc ML stp xp ra sp gp tp t0 t1 t2 (wz dlen) a7 s6 t3 t4 t5 t6) F (wz 0x1be38) fc None m' (seg_rom psegs)
    /\ munch (Wgl L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4).

Lemma gb1_len : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf base mc ML stp xp n dlen bits xb OL SL : Z) (FC DL : arr) (h0 h1 h2 h3 h4 : list byte)
    (ra sp gp tp s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  stree_view_n t stp -> 0 <= n < N -> n < sd_elems t -> 0 <= arr_get FC n < 65536 -> 1 <= bits <= 15 -> 0 <= xb < 16 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  evt psegs (gb1_len_post L s T h ovf base mc ML stp xp dlen (wrap64 (OL + arr_get FC n * (bits + xb)))
               (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xb)) else SL) ra sp gp tp s6 t4 t5 t6 F fc m)
      (MS (gbR L T h ovf base mc ML stp xp ra sp gp tp (wz (T + n * 4)) (wz bits) (wz xb) (wz dlen) (wz (n * 4)) s6 t3 t4 t5 t6)
          F (wz 0x1beb4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR GD MI LAY RT1 RT2 RN SV Rn RnE Rf Rb Rx ROL RSL.
  pose proof (munch_refl (Wgl L) m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY. unfold bD_cells in GD.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT.
  pose proof (u16arr_read psegs m T (avct FC DL N) (2 * n) _ (wa (T + n * 4)) ARR (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
  unfold gbR. zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2. zs2. zs2.
  rewrite (Z.mod_small (xb + bits) 4294967296) by lia. zs2.
  zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
  - subst stp. br_true.
    apply evt_done. unfold gb1_len_post, gbR, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    rewrite wz_wrap64. replace (OL + arr_get FC n * (bits + xb)) with (arr_get FC n * (xb + bits) + OL) by lia. exact GD.
  - br_false. destruct (RDS m0 n ltac:(eassumption) ltac:(lia)) as [RDl Rsl].
    zs2. zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2. rewrite (Z.mod_small (xb + stree_Len t n) 4294967296) by lia. zs2. zs2. zs2. zs2.
    apply evt_done. unfold gb1_len_post, gbR, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    rewrite !wz_wrap64. replace (OL + arr_get FC n * (bits + xb)) with (arr_get FC n * (xb + bits) + OL) by lia.
    replace (SL + arr_get FC n * (stree_Len t n + xb)) with ((xb + stree_Len t n) * arr_get FC n + SL) by lia. exact GD.
Qed.

Lemma slt_lxor : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^63 -> (Z.lxor a 9223372036854775808 <? Z.lxor b 9223372036854775808) = (a <? b).
Proof.
  intros a b Ha Hb. change 9223372036854775808 with (2^63). rewrite !lxor_sign by lia.
  destruct (Z.ltb_spec (a + 2^63) (b + 2^63)); destruct (Z.ltb_spec a b); try reflexivity; lia.
Qed.
Lemma ovf_incr : forall ML dlen, Z.lxor (Z.b2z (dlen <? ML)) 1 = (if ML <=? dlen then 1 else 0).
Proof. intros. destruct (Z.ltb_spec dlen ML); destruct (Z.leb_spec ML dlen); try reflexivity; lia. Qed.

Definition gb1_latch_post (L : dlay) (T h ovf' base mc ML stp xp : Z)
    (ra sp gp tp t0 t1 t2 a7 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a6 pcx m',
    ms' = MS (gbR L T (h + 1) ovf' base mc ML stp xp ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch [] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ ((pcx = 0x1be54 /\ h + 1 < 573) \/ (pcx = 0x1bf00 /\ h + 1 = 573)).

Lemma gb1_latch : forall (L : dlay) (T h ovf base mc ML stp xp dlen : Z)
    (ra sp gp tp t0 t1 t2 a7 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv psegs m -> 0 <= h < 573 -> 0 <= ovf < 2^30 -> 0 <= dlen < 65536 -> 1 <= ML <= 15 ->
  evt psegs (gb1_latch_post L T h (if ML <=? dlen then ovf + 1 else ovf) base mc ML stp xp ra sp gp tp t0 t1 t2 a7 s6 t3 t4 t5 t6 F fc m)
      (MS (gbR L T h ovf base mc ML stp xp ra sp gp tp t0 t1 t2 (wz dlen) a7 s6 t3 t4 t5 t6) F (wz 0x1be38) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros MI Rh Ro Rd RML.
  unfold gbR. zs2. zs2. zs2.
  rewrite slt_lxor, ovf_incr by lia.
  rewrite bv_swrap32_id by (destruct (ML <=? dlen); lia).
  replace (ovf + (if ML <=? dlen then 1 else 0)) with (if ML <=? dlen then ovf + 1 else ovf) by (destruct (ML <=? dlen); lia).
  zs2. zs2. zs2.
  replace (Z.land (h + 1) 4294967295) with (h + 1) by (change 4294967295 with (Z.ones 32); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
  zstep. br_cases K; reg_as (h + 2) (h + 1 + 1); reg_as (dl_As L + 3008 + 4 * h + 4) (dl_As L + 3008 + 4 * (h + 1)).
  - apply evt_done. unfold gb1_latch_post, gbR. do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. right. split; [reflexivity| lia].
  - apply evt_done. unfold gb1_latch_post, gbR. do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. left. split; [reflexivity| lia].
Qed.

Notation Wgb L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 3008); (dl_As L + 5881, dl_As L + 5968)] (only parsing).

Definition gb1_iter_post (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf mc stp xp : Z) (FC HP : arr) (HL HM : Z) (DP : arr) (f : nat) (R : deflate_state * Z)
    (ra sp gp tp s6 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 t4 h0 h1 h2 h3 h4 DL' BC' OL' SL' ovf' pcx m',
    ms' = MS (gbR L T (h + 1) ovf' (sd_extra_base t) mc (sd_max_length t) stp xp ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wgb L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4)
    /\ R = gen_bitlen_loop1 f (bt_upd s t FC DL' HP HL HM DP BC' OL' SL' mc) t mc (sd_extra_base t) (sd_max_length t) (h + 1) ovf'
    /\ gb1_ok t mc f (bt_upd s t FC DL' HP HL HM DP BC' OL' SL' mc) (h + 1) ovf'
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64 /\ ovf <= ovf' <= ovf + 1
    /\ ((pcx = 0x1be54 /\ h + 1 < 573) \/ (pcx = 0x1bf00 /\ h + 1 = 573)).

Lemma gb1_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf mc stp xp OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (f : nat) (R : deflate_state * Z)
    (ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp ->
  0 <= h < 573 -> 0 <= ovf <= h -> -1 <= mc < sd_elems t -> 0 <= arr_get HP h < N ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R = gen_bitlen_loop1 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) h ovf ->
  gb1_ok t mc (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) h ovf ->
  evt psegs (gb1_iter_post L s t T N h ovf mc stp xp FC HP HL HM DP f R ra sp gp tp s6 t5 t6 F fc m)
      (MS (gbR L T h ovf (sd_extra_base t) mc (sd_max_length t) stp xp ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz 0x1be54) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA BLC GD MI LAY RT1 RT2 EN LFC LDL LHP LBC XV SV Rh Ro Rmc Rn RBC RDL RFC ROL RSL ER OK.
  pose proof (munch_refl (Wgb L T N) m) as MU. pose proof (wmono_refl psegs m) as WM.
  assert (RML : 7 <= sd_max_length t <= 15) by (destruct t; cbv; split; discriminate).
  assert (RBASE : 0 <= sd_extra_base t < 300) by (destruct t; cbv; split; congruence).
  assert (RE : 19 <= sd_elems t <= 286 /\ tsize t = 2 * sd_elems t + 1) by (destruct t; cbv; repeat split; congruence).
  set (n := arr_get HP h) in *. set (dlen := arr_get DL (arr_get DL n)).
  set (bits := if sd_max_length t <=? dlen then sd_max_length t else dlen + 1). set (ovf' := if sd_max_length t <=? dlen then ovf + 1 else ovf).
  destruct (gb1_ok_step s t FC DL HP HL HM DP BC OL SL mc f h ovf n dlen bits ovf' OK ltac:(lia) eq_refl eq_refl eq_refl eq_refl) as [RD OK'].
  pose proof (gb1_model s t FC DL HP HL HM DP BC OL SL mc f h ovf R n dlen bits ovf' ER ltac:(lia) eq_refl eq_refl eq_refl eq_refl) as ER'.
  clear ER OK. rewrite <- EN in RD.
  assert (Rdl : 0 <= dlen < 65536) by (apply RDL; exact RD).
  assert (Rb : 1 <= bits <= 15) by (subst bits; destruct (Z.leb_spec (sd_max_length t) dlen); lia).
  assert (Ro' : ovf <= ovf' <= ovf + 1) by (subst ovf'; destruct (sd_max_length t <=? dlen); lia).
  assert (Rx0 : n <= mc -> 0 <= xbits t n < 16).
  { intros Hn. unfold xbits. destruct (Z.leb_spec (sd_extra_base t) n); [|lia]. destruct (XV m n MI ltac:(lia)) as [_ X]. exact X. }
  call (gb1_head L T N h ovf (sd_extra_base t) mc (sd_max_length t) stp xp n dlen bits FC DL HP).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. }
  1:{ exact Rh. } 1:{ reflexivity. } 1:{ exact Rn. } 1:{ exact RD. } 1:{ reflexivity. } 1:{ exact Rdl. } 1:{ lia. } 1:{ reflexivity. }
  pose proof (avct_zlength FC (arr_set DL n (wrap16 bits)) N ltac:(lia)) as LCT'. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (av16_zlength (arr_set BC bits (wrap16 (arr_get BC bits + 1))) 16 ltac:(lia)) as L16'.
  unfold gbR. zstep. br_cases K.
  - rewrite (proj2 (Z.ltb_lt mc n) K) in ER', OK'.
    call (gb1_latch L T h ovf (sd_extra_base t) mc (sd_max_length t) stp xp dlen).
    1:{ eassumption. } 1:{ exact Rh. } 1:{ lia. } 1:{ exact Rdl. } 1:{ lia. }
    fold ovf'.
    apply evt_done. unfold gb1_iter_post. do 12 eexists. exists (arr_set DL n (wrap16 bits)), BC, OL, SL, ovf'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [exact BLC|]. split; [exact GD|].
    split; [exact ER'|]. split; [exact OK'|]. split; [rewrite arr_len_set; exact LDL|]. split; [exact LBC|]. split; [exact RBC|].
    split; [intros i Hi; destruct (Z.eq_dec n i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RDL; exact Hi]|].
    split; [exact ROL|]. split; [exact RSL|]. split; [exact Ro'|]. assumption.
  - rewrite (proj2 (Z.ltb_ge mc n)) in ER', OK' by lia.
    pose proof (Rx0 ltac:(lia)) as Rx.
    call (gb1_cnt L t T h ovf mc stp xp n dlen bits BC).
    1:{ exact BLC. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rb. } 1:{ lia. } 1:{ lia. }
    match goal with HT : u8arr psegs ?mm T _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (gb1_len L s t T N h ovf (sd_extra_base t) mc (sd_max_length t) stp xp n dlen bits (xbits t n) OL SL FC (arr_set DL n (wrap16 bits)) h0 h1 h2 h3 h4);
      [exact HT| exact GD| eassumption| exact LAY| exact RT1| exact RT2| lia| exact SV| exact Rn| lia| apply RFC; exact Rn| exact Rb| exact Rx| exact ROL| exact RSL|] end.
    call (gb1_latch L T h ovf (sd_extra_base t) mc (sd_max_length t) stp xp dlen).
    1:{ eassumption. } 1:{ exact Rh. } 1:{ lia. } 1:{ exact Rdl. } 1:{ lia. }
    fold ovf'.
    apply evt_done. unfold gb1_iter_post. do 12 eexists. exists (arr_set DL n (wrap16 bits)), (arr_set BC bits (wrap16 (arr_get BC bits + 1))).
    exists (wrap64 (OL + arr_get FC n * (bits + xbits t n))), (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xbits t n)) else SL), ovf'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER'|]. split; [exact OK'|]. split; [rewrite arr_len_set; exact LDL|]. split; [rewrite arr_len_set; exact LBC|].
    split; [intros i Hi; destruct (Z.eq_dec bits i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RBC; exact Hi]|].
    split; [intros i Hi; destruct (Z.eq_dec n i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RDL; exact Hi]|].
    split; [apply wrap64_range|]. split; [destruct (stree_has t); [apply wrap64_range| exact RSL]|]. split; [exact Ro'|]. assumption.
Qed.

Definition gb1_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N mc stp xp : Z) (FC HP : arr) (HL HM : Z) (DP : arr) (R : deflate_state * Z)
    (ra sp gp tp s6 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 t4 h0 h1 h2 h3 h4 DL' BC' OL' SL' ovf' m',
    ms' = MS (gbR L T 573 ovf' (sd_extra_base t) mc (sd_max_length t) stp xp ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz 0x1bf00) fc None m' (seg_rom psegs)
    /\ munch (Wgb L T N) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC DL' HP HL HM DP BC' OL' SL' mc, ovf')
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64 /\ 0 <= ovf' <= 573.

Lemma gb1_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf mc stp xp OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state * Z) (m0 : mem)
    (ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> mem_inv psegs m -> dlay_ok L -> munch (Wgb L T N) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp ->
  0 <= h < 573 -> 573 - h <= Z.of_nat f -> 0 <= ovf <= h -> -1 <= mc < sd_elems t -> (forall k, h <= k < 573 -> 0 <= arr_get HP k < N) ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R = gen_bitlen_loop1 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) h ovf ->
  gb1_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) h ovf ->
  evt psegs (gb1_loop_post L s t T N mc stp xp FC HP HL HM DP R ra sp gp tp s6 t5 t6 F fc m0)
      (MS (gbR L T h ovf (sd_extra_base t) mc (sd_max_length t) stp xp ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz 0x1be54) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA BLC GD MI LAY MU WM RT1 RT2 EN LFC LDL LHP LBC XV SV Rh Hf Ro Rmc RHP RBC RDL RFC ROL RSL ER OK.
  { exfalso. lia. }
  pose proof (avct_zlength FC DL N ltac:(destruct t; subst N; cbv; discriminate)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  call (gb1_iter L s t T N h ovf mc stp xp OL SL FC DL HP HL HM DP BC h0 h1 h2 h3 h4 f R).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact BLC. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ exact LDL. }
  1:{ exact LHP. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ exact SV. } 1:{ exact Rh. } 1:{ exact Ro. } 1:{ exact Rmc. } 1:{ apply RHP; lia. } 1:{ exact RBC. } 1:{ exact RDL. } 1:{ exact RFC. }
  1:{ exact ROL. } 1:{ exact RSL. } 1:{ exact ER. } 1:{ exact OK. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - match goal with HT : u8arr psegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4),
                     ER' : R = gen_bitlen_loop1 f _ _ _ _ _ _ ?o', OK' : gb1_ok t mc f _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N (h + 1) o' mc stp xp ol' sl' FC dl' HP HL HM DP bc' g0 g1 g2 g3 g4 R m0);
        [exact HT| exact HPA| exact HB| exact HG| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact EN| exact LFC| assumption| exact LHP| assumption
        | exact XV| exact SV| lia| lia| lia| exact Rmc| intros k Hk; apply RHP; lia| assumption| assumption| exact RFC| assumption| assumption| exact ER'| exact OK'] end.
  - match goal with ER' : R = gen_bitlen_loop1 f _ _ _ _ _ _ _ |- _ => rewrite gb1_done in ER' by lia end.
    replace (h + 1) with 573 by lia.
    apply evt_done. unfold gb1_loop_post. do 12 eexists.
    match goal with HT : u8arr psegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4), ER' : R = (_, ?o') |- _ =>
      exists dl', bc', ol', sl', o'; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [exact ER'|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; lia end.
Qed.
