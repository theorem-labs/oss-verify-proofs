(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_bt1 Z_tr_bt2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel RefBuildTree1 RefBuildTree2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition bt_loop2_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc dsc : Z) (DL BC : arr) (HM MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a5 a6 a7 h0 h1 h2 h3 h4 FC' HP' HL' DP' OL' SL' mc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz (dl_As L)) a0 (wz dsc) a2 a3 (wz HL') a5 a6 a7
                  (wz T) (wz mc') (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bd34) fc None m' (seg_rom psegs)
    /\ munch (Wbt2 L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL'); C4 (wz HM)] /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC' DL HP' HL' HM DP' BC OL' SL' MC, mc')
    /\ arr_len FC' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ HL' = Z.max HL 2 /\ -1 <= mc' <= Z.max mc 2 /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64.

Lemma bt_loop2 : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc dsc stp HM OL SL MC : Z) (FC DL HP DP BC : arr) (h0 h1 h2 h3 h4 : list byte) (R : deflate_state * Z)
    (ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 3 <= N -> arr_len FC = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  stree_view t stp -> 0 <= HL < 2^31 -> -1 <= mc < 286 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R = build_tree_loop2 2 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t mc ->
  evt psegs (bt_loop2_post L s t T N HL mc dsc DL BC HM MC R ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (bt1R L T (sd_elems t) (sd_elems t) mc dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bd28) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA GC GD MI LAY RT1 RT2 RN LFC LHP LDP SV RHL Rmc ROL RSL ER.
  pose proof (munch_refl (Wbt2 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. unfold bt1R.
  zs2. zs2. zstep. br_cases K.
  - rewrite RefBuildTree2.L2_step in ER by lia. destruct (RefBuildTree2.l2node mc) as [node mc1] eqn:E1. symmetry in E1.
    zs2. zs2. zs2. zs2. zs2. zs2. zs2.
    assert (Rn1 : -1 <= mc1 <= Z.max mc 2) by (unfold RefBuildTree2.l2node in E1; destruct (Z.ltb_spec mc 2); inversion E1; lia).
    assert (ROL1 : 0 <= wrap64 (OL - 1) < 2^64) by apply wrap64_range.
    assert (RSL1 : 0 <= (if stree_has t then wrap64 (SL - stree_Len t node) else SL) < 2^64) by (destruct (stree_has t); [apply wrap64_range| exact RSL]).
    call (bt_l2_iter L s t T N HL mc dsc stp HM OL SL node mc1 FC DL HP DP h0 h1 h2 h3 h4).
    1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact SV. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact ROL. } 1:{ exact RSL. } 1:{ exact E1. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> K1]|[-> K1]] end.
    +
      rewrite RefBuildTree2.L2_step in ER by lia. destruct (RefBuildTree2.l2node mc1) as [node2 mc2] eqn:E2. symmetry in E2.
      assert (Rn2 : -1 <= mc2 <= Z.max mc 2) by (unfold RefBuildTree2.l2node in E2; destruct (Z.ltb_spec mc1 2); inversion E2; lia).
      match goal with HT : u8arr psegs ?mm T _, HA : u32arr psegs ?mm _ _, HD : u8arr psegs ?mm (dl_As L + 5308) _, HG : rw_cells psegs ?mm (dl_As L + 5300) _,
                       HGD : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells _ _ _ _ ?g0 ?g1 ?g2 ?g3 ?g4) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (bt_l2_iter L s t T N (HL + 1) mc1 dsc stp HM (wrap64 (OL - 1)) (if stree_has t then wrap64 (SL - stree_Len t node) else SL) node2 mc2
                (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node) (arr_set DP node (wrap8 0)) g0 g1 g2 g3 g4);
        [exact HT| exact HA| exact HD| exact HG| exact HGD| eassumption| exact LAY| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LFC| rewrite arr_len_set; exact LHP
        | rewrite arr_len_set; exact LDP| exact SV| lia| lia| exact ROL1| exact RSL1| exact E2|] end.
      match goal with H : _ \/ _ |- _ => destruct H as [[-> K2]|[-> K2]] end; [exfalso; lia|].
      cbn [build_tree_loop2] in ER.
      apply evt_done. unfold bt_loop2_post, bt2R. do 21 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
      split; [rewrite !arr_len_set; exact LFC|]. split; [rewrite !arr_len_set; exact LHP|]. split; [rewrite !arr_len_set; exact LDP|].
      split; [lia|]. split; [lia|]. split; [apply wrap64_range|]. destruct (stree_has t); [apply wrap64_range| exact RSL].
    + rewrite RefBuildTree2.L2_out in ER by lia.
      apply evt_done. unfold bt_loop2_post, bt2R. do 21 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
      split; [rewrite !arr_len_set; exact LFC|]. split; [rewrite !arr_len_set; exact LHP|]. split; [rewrite !arr_len_set; exact LDP|].
      split; [lia|]. split; [lia|]. split; [exact ROL1| exact RSL1].
  - rewrite RefBuildTree2.L2_out in ER by lia.
    apply evt_done. unfold bt_loop2_post. do 21 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|].
    split; [exact GC|]. split; [exact GD|]. split; [exact ER|].
    split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|]. split; [lia|]. split; [lia|]. split; [exact ROL| exact RSL].
Qed.
