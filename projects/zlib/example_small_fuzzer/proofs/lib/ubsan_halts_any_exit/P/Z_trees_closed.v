(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.

Module Z_tr_bits.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BitsModel2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tr_flush_bits_spec : tr_flush_bits_stmt.
Proof.
  unfold tr_flush_bits_stmt. intros until m. intros ST MI BI ROOM ->. unfold Z_TR_FLUSH_BITS.
  destruct BI as (RBV & RBB & RPD). unfold tr_flush_bits in ROOM.
  pose proof (munch_refl [(dl_As L, dl_As L + DS_SIZE); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + DS_PEND)] m) as MUf.
  open_DST ST. lay_open LAY. pose proof (ln_pend _ LENS) as LNP.
  open_D GD.
  do 3 zstep. zs. do 2 zstep.
  if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  -
    do 2 zstep.
    if_cases K2; zify_cond K2; rewrite ?signed_wz in K2 by lia.
    +
      zstep. apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      unfold tr_flush_bits. rewrite bi_flush_eq0 by lia. rewrite upd4_self.
      constructor; [exact GA| exact GB| exact GC| exists hD0, hD1, hD2, hD3, hD4; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY].
    +
      rewrite bi_flush_eq8, upd4_pending in ROOM by lia.
      open_A GA. open_pend Gpend.
      do 2 zstep. rd_c2 GD 55%nat 0. zstep. do 3 zstep.
      pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (ds_bi_buf s)) ltac:(apply b0_val_w; lia).
      rd_c2 GD 55%nat 1. zstep. zs. rewrite (bv8_small (Z.shiftr (ds_bi_buf s) 8)) by (apply shr8_small; lia).
      do 4 zstep.
      apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      unfold tr_flush_bits. rewrite bi_flush_eq8 by lia. tr_groups MUf WM.
      constructor; [eexists _, _, _, _, _; unfold dsA_cells, upd4; dsred; close_cells GA| exact GB| exact GC
                   | eexists _, _, _, _, _; unfold dsD_cells, upd4; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| unfold dpend, upd4; dsred; exact Gpend| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
  -
    rewrite bi_flush_eq16, upd4_pending in ROOM by lia.
    open_A GA. open_pend Gpend.
    do 3 zstep. rd_c2 GD 55%nat 0. zstep. do 3 zstep.
    pb_store Gpend (ds_pending_buf s) 65536 (dl_Ab L) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255)) ltac:(apply b0_val_land; lia).
    do 2 zstep. rd_c2 GD 55%nat 1. zstep. do 3 zstep.
    pb_store Gpend (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255))) 65536 (dl_Ab L) (ds_pending s + 1)
             (wrap8 (Z.shiftr (wrap16 (ds_bi_buf s)) 8)) ltac:(apply b1_val; lia).
    do 4 zstep.
    apply evt_done. unfold tr_flush_bits_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    unfold tr_flush_bits. rewrite bi_flush_eq16 by lia. tr_groups MUf WM.
    constructor; [eexists _, _, _, _, _; unfold dsA_cells, upd4; dsred; close_cells GA| exact GB| exact GC
                 | eexists _, _, _, _, _; unfold dsD_cells, upd4; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| unfold dpend, upd4; dsred; exact Gpend| close_lens_with LENS ltac:(unfold upd4)| exact LAY].
Qed.
End Z_tr_bits.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_fb11.

Module Z_tr_bt11.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_emit Z_tr_cb3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition bt_loop2_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc dsc : Z) (DL BC : arr) (HM MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a5 a6 a7 h0 h1 h2 h3 h4 FC' HP' HL' DP' OL' SL' mc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz (dl_As L)) a0 (wz dsc) a2 a3 (wz HL') a5 a6 a7
                  (wz T) (wz mc') (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b9b4) fc None m' (seg_rom psegs)
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
      (MS (bt1R L T (sd_elems t) (sd_elems t) mc dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b9a8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA GC GD MI LAY RT1 RT2 RN LFC LHP LDP SV RHL Rmc ROL RSL ER.
  pose proof (munch_refl (Wbt2 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. unfold bt1R.
  zs2. zs2. zstep. br_cases K.
  - rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.L2_step in ER by lia. destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.l2node mc) as [node mc1] eqn:E1. symmetry in E1.
    zs2. zs2. zs2. zs2. zs2. zs2. zs2.
    assert (Rn1 : -1 <= mc1 <= Z.max mc 2) by (unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.l2node in E1; destruct (Z.ltb_spec mc 2); inversion E1; lia).
    assert (ROL1 : 0 <= wrap64 (OL - 1) < 2^64) by apply wrap64_range.
    assert (RSL1 : 0 <= (if stree_has t then wrap64 (SL - stree_Len t node) else SL) < 2^64) by (destruct (stree_has t); [apply wrap64_range| exact RSL]).
    call (bt_l2_iter L s t T N HL mc dsc stp HM OL SL node mc1 FC DL HP DP h0 h1 h2 h3 h4).
    1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact SV. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact ROL. } 1:{ exact RSL. } 1:{ exact E1. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> K1]|[-> K1]] end.
    +
      rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.L2_step in ER by lia. destruct (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.l2node mc1) as [node2 mc2] eqn:E2. symmetry in E2.
      assert (Rn2 : -1 <= mc2 <= Z.max mc 2) by (unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.l2node in E2; destruct (Z.ltb_spec mc1 2); inversion E2; lia).
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
    + rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.L2_out in ER by lia.
      apply evt_done. unfold bt_loop2_post, bt2R. do 21 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
      split; [rewrite !arr_len_set; exact LFC|]. split; [rewrite !arr_len_set; exact LHP|]. split; [rewrite !arr_len_set; exact LDP|].
      split; [lia|]. split; [lia|]. split; [exact ROL1| exact RSL1].
  - rewrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.L2_out in ER by lia.
    apply evt_done. unfold bt_loop2_post. do 21 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|].
    split; [exact GC|]. split; [exact GD|]. split; [exact ER|].
    split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|]. split; [lia|]. split; [lia|]. split; [exact ROL| exact RSL].
Qed.
End Z_tr_bt11.

Module Z_tr_bt18.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_cb3 F_memset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt10 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt9.Z_tr_bt12 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt14 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt15 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt16 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).



Lemma blc_zero : forall BC, arr_len BC = 16 -> u16s (av16 (arr_fill BC 0 16 0) 16) = repeat (Z_to_bv 8 0) 32.
Proof.
  intros BC LBC. unfold av16. rewrite zseq_16. cbn [map]. rewrite !arr_get_fill. unfold arr_inb. rewrite !LBC. cbn. reflexivity.
Qed.
Lemma blc_zero_range : forall BC i, arr_len BC = 16 -> 0 <= i < 16 -> 0 <= arr_get (arr_fill BC 0 16 0) i < 65536.
Proof.
  intros BC i LBC Hi. rewrite arr_get_fill. unfold arr_inb. rewrite LBC.
  replace ((0 <=? i) && (i <? 0 + Z.max 0 16) && ((0 <=? i) && (i <? 16))) with true; [lia|].
  symmetry. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt. lia.
Qed.

Definition gb_tail (t : tree_id) (mc : Z) (R1 : deflate_state * Z) : deflate_state :=
  let (X10, ovf) := R1 in
  if ovf =? 0 then X10
  else gen_bitlen_loop3 (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) t mc (sd_max_length t) HEAP_SIZE.
Lemma gb_tail_0 : forall t mc X, gb_tail t mc (X, 0) = X.
Proof. intros. reflexivity. Qed.
Lemma gb_tail_nz : forall t mc X ovf, ovf <> 0 ->
  gb_tail t mc (X, ovf) = gen_bitlen_loop3 (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X (sd_max_length t) ovf) t mc (sd_max_length t) 573.
Proof. intros t mc X ovf H. unfold gb_tail. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma gen_bitlen_flat : forall s t FC DL HP HL hm DP BC OL SL mc,
  gen_bitlen (bt_upd s t FC DL HP HL hm DP BC OL SL mc) t
  = gb_tail t mc (gen_bitlen_loop1 573 (bt_upd s t FC (arr_set DL (arr_get HP hm) (wrap16 0)) HP HL hm DP (arr_fill BC 0 16 0) OL SL mc) t mc
                    (sd_extra_base t) (sd_max_length t) (hm + 1) 0).
Proof.
  intros. unfold gen_bitlen, gb_tail. rewrite bt_max_code, bt_bl_count, bt_set_bl_count, bt_heap_max, bt_heap_get, bt_set_Len, bt_heap_max.
  change (MAX_BITS + 1) with 16.
  destruct (gen_bitlen_loop1 573 _ t mc _ _ (hm + 1) 0) as [X10 ovf]. reflexivity.
Qed.


Notation Wpre L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 5308)] (only parsing).

Definition gb_pre_post (L : dlay) (T N hm dsc SD mc stp xp : Z) (t : tree_id) (FC DL HP BC : arr) (hh : list byte)
    (ra sp gp tp s6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (gbR L T (hm + 1) 0 (sd_extra_base t) mc (sd_max_length t) stp xp (wz 0x1bde0) sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz 0x1be54) fc None m' (seg_rom psegs)
    /\ munch (Wpre L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC (arr_set DL (arr_get HP 1) (wrap16 0)) N))
    /\ u32arr psegs m' (dl_As L + 3008) (av32 (arr_set HP hm (arr_get HP 1)) 573)
    /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 (arr_fill BC 0 16 0) 16))
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)]
    /\ rw_cells psegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz SD)].

Lemma gb_pre : forall (L : dlay) (T N hm node dsc SD mc stp xp : Z) (t : tree_id) (FC DL HP BC : arr) (hh : list byte)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz (hm + 1))] ->
  rw_cells psegs m dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz SD)] ->
  rw_cells psegs m SD [C8 (wz stp); C8 (wz xp); C4 (wz (sd_extra_base t)); C4 (wz (sd_elems t)); C4 (wz (sd_max_length t))] ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  0 <= hm <= 570 -> 0 <= arr_get HP 1 < N -> -1 <= mc < N -> dsc = dl_As L + bt_desc t -> 0x10000 <= SD -> SD + 32 <= 0x5b000 -> 0 <= stp < 2^63 -> 0 <= xp < 2^63 ->
  evt psegs (gb_pre_post L T N hm dsc SD mc stp xp t FC DL HP BC hh ra sp gp tp (wz (dl_As L + 3008)) F fc m)
      (MS (l4R L T 1 node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bd98) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA BLC GC Gdsc Gsd MI LAY RT1 RT2 RN LFC LDL LHP LBC Rhm Rh1 Rmc Edsc RSD1 RSD2 Rstp Rxp.
  pose proof (munch_refl (Wpre L T N) m) as MU. pose proof (wmono_refl psegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (Bs : dl_As L + 5968 <= 0x10000 \/ 0x5b000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & Bs); exact Bs).
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn [bt_desc]; lia).
  assert (RE : sd_extra_base t <= 257 /\ 0 <= sd_extra_base t /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15)
    by (destruct t; cbn [sd_extra_base sd_elems sd_max_length]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (u32arr_read psegs m _ (av32 HP 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD1.
  unfold l4R. zs2. zs2. zs2. zs2. shl_norm. zstep. zs2. zs2.
  h32_store HPA HP 573 (dl_As L + 3008) hm (arr_get HP 1) ltac:(reflexivity).
  zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. clear Gsd.
  zstep.
  apply rw_cells_of_u8arr in BLC. change (length (u16s (av16 BC 16))) with (Z.to_nat 32) in BLC.
  call memset_callZ.
  1:{ exact BLC. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  match goal with H : rw_cells psegs ?mm (dl_As L + 2976) [CB _ _] |- _ =>
    change (Z.to_nat 32) with 32%nat in H; change (0 mod 256) with 0 in H; apply (u8arr_of_rw_cells psegs) in H; rewrite <- (blc_zero BC LBC) in H; rename H into BLC0 end.
  pose proof (av16_zlength (arr_fill BC 0 16 0) 16 ltac:(lia)) as L16z.
  zs2. zs2. shl_norm. zs2.
  match goal with HA : u32arr psegs ?mm (dl_As L + 3008) (av32 ?hp 573) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read psegs mm _ (av32 hp 573) hm _ (wa (dl_As L + 3008 + hm * 4)) HA (av32_nth hp 573 hm ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDh;
    rewrite arr_get_set_same in RDh by lia end.
  zs2. zs2. shl_norm. zs2.
  ct_store_dl ARR FC DL N T (arr_get HP 1) (wrap16 0) ltac:(reflexivity).
  zs2. zs2. zstep. br_false.
  zs2. zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2. zs2. zs2. zs2. zstep.
  reg_as (hm + 2) (hm + 1 + 1). reg_as (hm * 4 + (dl_As L + 2976) + 36) (dl_As L + 3008 + 4 * (hm + 1)).
  apply evt_done. unfold gb_pre_post, gbR. do 10 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact ARR|]. split; [eassumption|]. split; [exact BLC0|]. split; [eassumption| eassumption].
Qed.


Definition gb_main_post (L : dlay) (s : deflate_state) (t : tree_id) (T N hm mc stp xp : Z) (FC HP : arr) (HL : Z) (DP : arr) (R : deflate_state)
    (ra sp gp tp s6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s5x s9x t3 t4 t5 t6 DL' BC' OL' SL' g0 g1 g2 g3 g4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1x a0 a1 a2 a3 a4 a5 a6 a7 (wz T) (wz mc) (wz (dl_As L + 5300)) s5x s6 (wz T) (wz mc) s9x (wz stp) (wz xp) t3 t4 t5 t6)
             F (wz 0x1bff8) fc None m' (seg_rom psegs)
    /\ munch (Wgb L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ R = bt_upd s t FC DL' HP HL hm DP BC' OL' SL' mc
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536)
    /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64.

Lemma gb_main : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N hm mc stp xp OL SL : Z) (FC DL HP : arr) (HL : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R1 : deflate_state * Z) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> rw_cells psegs m (bv_unsigned sp) [C8 (wz (dl_As L + 2047))] ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp ->
  0 <= hm <= 570 -> -1 <= mc < sd_elems t -> (forall k, hm + 1 <= k < 573 -> 0 <= arr_get HP k < N) ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 144 < 2^63 ->
  R1 = gen_bitlen_loop1 573 (bt_upd s t FC DL HP HL hm DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) (hm + 1) 0 ->
  gb1_ok t mc 573 (bt_upd s t FC DL HP HL hm DP BC OL SL mc) (hm + 1) 0 ->
  (forall X10 ovf, R1 = (X10, ovf) -> ovf <> 0 ->
     gb2_ok (sd_max_length t) 573 X10 ovf /\ gb3_ok t mc (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) (sd_max_length t) 573) ->
  R = gb_tail t mc R1 ->
  evt psegs (gb_main_post L s t T N hm mc stp xp FC HP HL DP R ra sp gp tp s6 F fc m)
      (MS (gbR L T (hm + 1) 0 (sd_extra_base t) mc (sd_max_length t) stp xp ra sp gp tp t0 t1 t2 a6 a7 s6 t3 t4 t5 t6) F (wz 0x1be54) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA BLC GD F0 MI LAY RT1 RT2 EN LFC LDL LHP LBC XV SV Rhm Rmc RHP RBC RDL RFC ROL RSL SEP RSP ER1 OK1 OK23 ER.
  pose proof (munch_refl (Wgb L T N) m) as MU. pose proof (wmono_refl psegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (RE : sd_extra_base t <= 257 /\ 0 <= sd_extra_base t /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15 /\ N = 2 * sd_elems t + 1)
    by (subst N; destruct t; cbn [sd_extra_base sd_elems sd_max_length tsize]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  call (gb1_loop 573 L s t T N (hm + 1) 0 mc stp xp OL SL FC DL HP HL hm DP BC h0 h1 h2 h3 h4 R1 m).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact BLC. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ exact SV. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact RHP. } 1:{ exact RBC. } 1:{ exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. } 1:{ exact RSL. }
  1:{ exact ER1. } 1:{ exact OK1. }
  match goal with H : R1 = (bt_upd _ _ _ ?dl' _ _ _ _ ?bc' ?ol' ?sl' _, ?ovf') |- _ => rename H into ER1'; clear ER1 end.
  unfold gbR. zstep. br_cases K.
  -
    lazymatch type of ER1' with R1 = (?X, ?o) => rewrite ER1' in ER; replace o with 0 in ER by lia; rewrite gb_tail_0 in ER end.
    apply evt_done. unfold gb_main_post. do 18 eexists.
    match goal with HT : u8arr psegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4) |- _ =>
      exists dl', bc', ol', sl', g0, g1, g2, g3, g4; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [exact ER|] end.
    repeat (split; [assumption|]). assumption.
  -
    lazymatch type of ER1' with R1 = (?X, ?o) => destruct (OK23 X o ER1' ltac:(lia)) as [OK2 OK3]; rewrite ER1' in ER; rewrite (gb_tail_nz t mc X o) in ER by lia end.
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2.
    rewrite lor_hi32 by lia. reg_as (sd_max_length t * 4294967296 + 4294967295 + 1) ((sd_max_length t + 1) * 4294967296).
    reg_as (dl_As L + (sd_max_length t * 2 + 2976)) (dl_As L + 2976 + sd_max_length t * 2).
    lazymatch type of ER1' with R1 = (?X, ?o) => name_term R2 ER2 (gen_bitlen_loop2 573 X (sd_max_length t) o) end.
    match goal with HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)), HT : u8arr psegs ?mm T (u16s (avct FC ?dl' N)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'; pose proof (avct_zlength FC dl' N ltac:(lia)) as LCT' end.
    lazymatch type of ER1' with R1 = (bt_upd _ _ _ ?dl' _ _ _ _ ?bc' ?ol' ?sl' _, ?o) =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (gl2_loop 573 L s t T o mc (sd_max_length t) FC dl' HP HL hm DP bc' ol' sl' R2 mm) end end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ assumption. } 1:{ assumption. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ER2. } 1:{ exact OK2. }
    match goal with H : R2 = bt_upd _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite H in ER, OK3; clear H ER2 end.
    unfold gl2R. zstep. br_false. zs2. zs2. reg_as (dl_As L + 2047 + 957) (dl_As L + 3004). zs2. zstep.
    match goal with HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'' end.
    lazymatch type of ER1' with R1 = (bt_upd _ _ _ ?dl' _ _ _ _ _ ?ol' ?sl' _, _) =>
    lazymatch goal with HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)), HG : rw_cells psegs ?mm' (dl_As L + 5881) (bD_cells L s _ _ ?g0 ?g1 ?g2 ?g3 ?g4)
      |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (g3_loop (Z.to_nat (sd_max_length t)) L s t T N (sd_max_length t) 573 mc ol' sl' FC dl' HP HL hm DP bc' g0 g1 g2 g3 g4 R mm) end end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ exact LHP. } 1:{ assumption. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ exact RFC. } 1:{ assumption. } 1:{ exact ER. } 1:{ exact OK3. }
    unfold g3oR. apply evt_done. unfold gb_main_post. do 18 eexists.
    match goal with HT : u8arr psegs ?mm T (u16s (avct FC ?dl'' N)), HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc'' 16)),
                     HG : rw_cells psegs ?mm (dl_As L + 5881) (bD_cells L s ?ol'' ?sl'' ?g0 ?g1 ?g2 ?g3 ?g4) |- _ =>
      exists dl'', bc'', ol'', sl'', g0, g1, g2, g3, g4; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [assumption|] end.
    repeat (split; [assumption|]). all: lia.
Qed.


Notation WpB L T N sp := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 5308); (dl_As L + 5881, dl_As L + 5968); (bv_unsigned sp + 8, bv_unsigned sp + 40)] (only parsing).

Definition partB_post (L : dlay) (s : deflate_state) (t : tree_id) (T N hm dsc SD mc : Z) (HP7 DP : arr) (hh : list byte) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) FC' DL' BC' OL' SL' g0 g1 g2 g3 g4 junk' m',
    ms' = MS (mkR x1 sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz T) s3 (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1c158) fc None m' (seg_rom psegs)
    /\ munch (WpB L T N sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP7 573) /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ rw_cells psegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz SD)] /\ rw_cells psegs m' (bv_unsigned sp + 8) [CB 32 junk']
    /\ R = bt_upd s t FC' DL' HP7 1 hm DP BC' OL' SL' mc /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len BC' = 16.

Lemma partB : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N hm node dsc SD mc stp xp OL SL : Z) (FC DL HP DP BC : arr) (hh h0 h1 h2 h3 h4 junk : list byte)
    (R : deflate_state)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  let HP7 := arr_set HP hm (arr_get HP 1) in
  let X7 := bt_upd s t FC DL HP7 1 hm DP BC OL SL mc in
  let X9 := bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) HP7 1 hm DP (arr_fill BC 0 16 0) OL SL mc in
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz (hm + 1))] -> rw_cells psegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  rw_cells psegs m dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz SD)] ->
  rw_cells psegs m SD [C8 (wz stp); C8 (wz xp); C4 (wz (sd_extra_base t)); C4 (wz (sd_elems t)); C4 (wz (sd_max_length t))] ->
  rw_cells psegs m (bv_unsigned sp) [C8 (wz (dl_As L + 2047))] -> rw_cells psegs m (bv_unsigned sp + 8) [CB 32 junk] ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp -> 0 <= stp < 2^63 -> 0 <= xp < 2^63 -> 0x10000 <= SD -> SD + 32 <= 0x5b000 -> dsc = dl_As L + bt_desc t ->
  0 <= hm <= 570 -> 0 <= arr_get HP 1 < N -> -1 <= mc < sd_elems t ->
  (forall k, hm + 1 <= k < 573 -> 0 <= arr_get HP7 k < N) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 144 < 2^63 ->
  gb1_ok t mc 573 X9 (hm + 1) 0 ->
  (forall X10 ovf, gen_bitlen_loop1 573 X9 t mc (sd_extra_base t) (sd_max_length t) (hm + 1) 0 = (X10, ovf) -> ovf <> 0 ->
     gb2_ok (sd_max_length t) 573 X10 ovf /\ gb3_ok t mc (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) (sd_max_length t) 573) ->
  (forall i, 0 <= i <= mc -> 0 <= Len (gen_bitlen X7 t) t i <= 15) ->
  R = gen_codes (gen_bitlen X7 t) t mc ->
  evt psegs (partB_post L s t T N hm dsc SD mc HP7 DP hh R sp gp tp F fc m)
      (MS (l4R L T 1 node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bd98) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HP7 X7 X9 ARR HPA BLC GC GD Gdsc Gsd F0 F1 MI LAY RT1 RT2 EN LFC LDL LHP LBC XV SV Rstp Rxp RSD1 RSD2 Edsc Rhm Rh1 Rmc RHP RDL RFC ROL RSL SEP RSP
    OK1 OK23 LEN ER. subst HP7 X7 X9.
  pose proof (munch_refl (WpB L T N sp) m) as MU. pose proof (wmono_refl psegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (RE : 19 <= sd_elems t <= 286 /\ N = 2 * sd_elems t + 1)
    by (subst N; destruct t; cbn [sd_elems tsize]; unfold L_CODES, D_CODES, BL_CODES; lia).
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn [bt_desc]; lia).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  rewrite (gen_bitlen_flat s t FC DL (arr_set HP hm (arr_get HP 1)) 1 hm DP BC OL SL mc) in ER, LEN.
  rewrite (arr_get_set_same HP hm (arr_get HP 1)) in ER, LEN by lia.
  name_term R1 ER1 (gen_bitlen_loop1 573 (bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP hm (arr_get HP 1)) 1 hm DP (arr_fill BC 0 16 0) OL SL mc) t mc
                       (sd_extra_base t) (sd_max_length t) (hm + 1) 0).
  name_term RB ERB (gb_tail t mc R1).
  call (gb_pre L T N hm node dsc SD mc stp xp t FC DL HP BC hh).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact BLC. } 1:{ exact GC. } 1:{ exact Gdsc. } 1:{ exact Gsd. } 1:{ exact MI. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LBC. }
  1:{ exact Rhm. } 1:{ exact Rh1. } 1:{ lia. } 1:{ exact Edsc. } 1:{ exact RSD1. } 1:{ exact RSD2. } 1:{ exact Rstp. } 1:{ exact Rxp. }
  pose proof (avct_zlength FC (arr_set DL (arr_get HP 1) (wrap16 0)) N ltac:(lia)) as LCT'.
  pose proof (av32_zlength (arr_set HP hm (arr_get HP 1)) 573 ltac:(lia)) as L32'. pose proof (av16_zlength (arr_fill BC 0 16 0) 16 ltac:(lia)) as L16'.
  unfold gbR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (gb_main L s t T N hm mc stp xp OL SL FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP hm (arr_get HP 1)) 1 DP (arr_fill BC 0 16 0) h0 h1 h2 h3 h4 R1 RB) end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact GD. } 1:{ exact F0. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ rewrite arr_len_set. exact LDL. } 1:{ rewrite arr_len_set. exact LHP. } 1:{ rewrite arr_len_fill. exact LBC. }
  1:{ exact XV. } 1:{ exact SV. } 1:{ exact Rhm. } 1:{ exact Rmc. } 1:{ exact RHP. } 1:{ intros i Hi. apply blc_zero_range; [exact LBC| exact Hi]. }
  1:{ apply arr_set_range16. exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. } 1:{ exact RSL. } 1:{ exact SEP. } 1:{ exact RSP. }
  1:{ exact ER1. } 1:{ exact OK1. } 1:{ exact OK23. } 1:{ exact ERB. }
  match goal with H : RB = bt_upd _ _ _ ?dl' _ _ _ _ ?bc' _ _ _ |- _ => rewrite H in ER, LEN; clear H ERB;
    pose proof (avct_zlength FC dl' N ltac:(lia)) as LCT''; pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'' end.
  match goal with HG : rw_cells psegs _ (dl_As L + 5881) (bD_cells _ _ _ _ _ _ _ _ _) |- _ => unfold bD_cells in HG end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of ER with R = gen_codes (bt_upd s t FC ?dl' ?hp' 1 hm DP ?bc' ?ol' ?sl' mc) t mc =>
    call (gcs_phase s t L T N mc FC dl' hp' 1 hm DP bc' ol' sl' mc R junk) end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ exact F1. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. }
  1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact SEP. } 1:{ lia. } 1:{ lia. }
  1:{ intros i Hi. pose proof (LEN i Hi) as Li. rewrite bt_Len in Li. exact Li. } 1:{ exact ER. }
  apply evt_done. unfold partB_post. do 24 eexists.
  match goal with HT : u8arr psegs ?mm T (u16s (avct ?fc' ?dl' N)), HB : u8arr psegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                   HG : rw_cells psegs ?mm (dl_As L + 5881) [CB 7 ?g0; _; _; _; _; CB 4 ?g1; C8 (wz ?ol'); C8 (wz ?sl'); _; _; _; CB 2 ?g2; _; CB 4 ?g3; _; _; CB 4 ?g4; _],
                   HF : rw_cells psegs ?mm (bv_unsigned sp + 8) [CB 32 ?j] |- _ =>
    exists fc', dl', bc', ol', sl', g0, g1, g2, g3, g4, j; eexists;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [eassumption|]; split; [exact HB|];
    split; [eassumption|]; split; [exact HG|]; split; [eassumption|]; split; [exact HF|] end.
  repeat (split; [assumption|]). assumption.
Qed.
End Z_tr_bt18.

Module Z_tr_bt19.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit.Z_tr_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_emit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3.Z_tr_scan1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_cb3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt7 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13.Z_tr_bt10 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_closed.Z_tr_bt11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt16 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_closed.Z_tr_bt18.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefBuildTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.TreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BuildTreeModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenBitlenModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.GenCodesModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_tr_bt17.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).


Notation WBT L T N dsc lo sp := [(lo%Z, bv_unsigned sp); (T%Z, (T + 4 * N)%Z); ((dsc + 8)%Z, (dsc + 12)%Z); (dl_As L + 2976, dl_As L + 5968)] (only parsing).

Definition body_post (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh : list byte) (R : deflate_state)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (FC' DL' HP' DP' BC' : arr) (OL' SL' hm mc : Z) (g0 g1 g2 g3 g4 : list byte) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch (WBT L T N dsc lo sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ rw_cells psegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))]
    /\ R = bt_upd s t FC' DL' HP' 1 hm DP' BC' OL' SL' mc
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ arr_len BC' = 16.

Lemma build_tree_body : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh g0 g1 g2 g3 g4 : list byte) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct (tree_fc s t) (tree_dl s t) N)) -> u32arr psegs m (dl_As L + 3008) (av32 (ds_heap s) 573) ->
  u8arr psegs m (dl_As L + 5308) (av8 (ds_depth s) 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 (ds_bl_count s) 16)) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz (ds_heap_len s)); C4 (wz (ds_heap_max s))] ->
  rw_cells psegs m (dl_As L + 5881) (bD_cells L s (ds_opt_len s) (ds_static_len s) g0 g1 g2 g3 g4) ->
  rw_cells psegs m dsc [C8 (wz T); C4 (wz (max_code s t)); CB 4 hh; C8 (wz (SDA t))] ->
  mem_inv psegs m -> relro_clean m -> dlay_ok L ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe s t -> T = dl_As L + toff t -> N = tsize t -> dsc = dl_As L + bt_desc t ->
  arr_len (tree_fc s t) = N -> arr_len (tree_dl s t) = N -> arr_len (ds_heap s) = 573 -> arr_len (ds_depth s) = 573 -> arr_len (ds_bl_count s) = 16 ->
  a0 = wz (dl_As L) -> a1 = wz dsc ->
  R = build_tree s t ->
  evt psegs (body_post L s t T N dsc lo hh R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz Z_BUILD_TREE) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA BLC GC GD Gdsc MI RC LAY STK LO AL BEL SAFE ET EN Edsc LFC LDL LHP LDP LBC -> -> ER0.
  unfold Z_BUILD_TREE.
  pose proof (munch_refl (WBT L T N dsc lo sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0.
  assert (BsK : dl_As L + 5968 <= 0x10000 \/ 0x5b000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & X); exact X).
  pose proof (toff_tsize t) as Rtt. pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.elems_range t) as RE. pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.tsize_elems t) as EN2.
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn; lia).
  assert (RML : 7 <= sd_max_length t <= 15 /\ 0 <= sd_extra_base t <= 257) by (destruct t; cbn; unfold MAX_BITS, MAX_BL_BITS, LITERALS; lia).
  pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.SDA_range t) as RSDA. pose proof (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_bt17.Z_tr_bt19p.STP_range t) as RSTP. pose proof (XP_range t) as RXP.
  destruct (safe_s0 s t SAFE) as (RFC0 & ROL0 & RSL0). rewrite <- EN in RFC0.
  pose proof (avct_zlength (tree_fc s t) (tree_dl s t) N ltac:(lia)) as LCT. pose proof (av32_zlength (ds_heap s) 573 ltac:(lia)) as L32.
  pose proof (av8_zlength (ds_depth s) 573 ltac:(lia)) as L8. pose proof (av16_zlength (ds_bl_count s) 16 ltac:(lia)) as L16.
  unfold bD_cells in GD.
  carve_frame 144%nat STK.
  zstep.
  do 13 zstep.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -144)) = bv_unsigned sp + -144) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  zs2. zs2. zs2. zs2. zs2. zs2.
  pose proof (sdesc_relro t _ (relro_clean_munch _ _ _ RC MU ltac:(cbn [disjoint_from]; unfold RELRO_LO, RELRO_HI; lia))) as Gsd. unfold sd_cells in Gsd.
  zs2. zs2. clear Gsd.
  zs2. zs2. zstep. zstep. zs2. zstep. br_false.
  zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zstep.
  reg_as (T + 2 + sd_elems t * 4) (T + 4 * sd_elems t + 2). reg_as (dl_As L + 5308) (dl_As L + 5308 + 0). reg_as (T + 2) (T + 4 * 0 + 2).
  name_term R1 ER1 (L1 t (btX0 s t) 0 (-1)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (bt_loop1 (Z.to_nat (sd_elems t) - 1) L s t T N dsc (STP t) (tree_fc s t) (ds_bl_count s) 573 (ds_opt_len s) (ds_static_len s) (max_code s t) R1 mm
                   (tree_dl s t) (ds_heap s) 0 (ds_depth s) 0 (-1)) end.
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact RFC0. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ unfold btX0 in ER1. exact ER1. }
  match goal with H : R1 = (bt_upd _ _ _ ?dl1 ?hp1 ?hl1 _ ?dp1 _ _ _ _, ?mc1) |- _ =>
    rename H into ER1';
    assert (E1 : build_tree_loop1 (Z.to_nat (sd_elems t)) (btX0 s t) t (sd_elems t) 0 (-1) = (bt_upd s t (tree_fc s t) dl1 hp1 hl1 573 dp1 (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t), mc1))
      by (rewrite <- ER1', ER1; unfold L1; rewrite Z.sub_0_r; reflexivity);
    clear ER1 ER1';
    pose proof (avct_zlength (tree_fc s t) dl1 N ltac:(lia)) as LCT1; pose proof (av32_zlength hp1 573 ltac:(lia)) as L32_1; pose proof (av8_zlength dp1 573 ltac:(lia)) as L8_1 end.
  lazymatch type of E1 with _ = (?X1, ?mc1) => name_term R2 ER2 (build_tree_loop2 2 X1 t mc1) end.
  unfold bt1R.
  lazymatch type of E1 with _ = (bt_upd _ _ _ ?dl1 ?hp1 ?hl1 _ ?dp1 _ _ _ _, ?mc1) =>
    call (bt_loop2 L s t T N hl1 mc1 dsc (STP t) 573 (ds_opt_len s) (ds_static_len s) (max_code s t) (tree_fc s t) dl1 hp1 dp1 (ds_bl_count s) g0 g1 g2 g3 g4 R2) end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact GD. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ assumption. } 1:{ apply stree_view_of. } 1:{ lia. } 1:{ lia. } 1:{ exact ROL0. } 1:{ exact RSL0. }
  1:{ exact ER2. }
  match goal with H : R2 = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) |- _ =>
    rename H into ER2'; pose proof ER2' as E2; rewrite ER2 in E2; clear ER2 ER2' R2;
    pose proof (avct_zlength fc2 dl1 N ltac:(lia)) as LCT2; pose proof (av32_zlength hp2 573 ltac:(lia)) as L32_2; pose proof (av8_zlength dp2 573 ltac:(lia)) as L8_2 end.
  match goal with HG : rw_cells psegs _ (dl_As L + 5881) (bD_cells _ _ _ _ _ _ _ _ _) |- _ => unfold bD_cells in HG; rename HG into GD2 end.
  destruct (safe_s3 s t SAFE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1 E2) as (PQ2 & RDP2 & RFC2 & S7). rewrite <- EN in PQ2, RFC2.
  zs2. zstep. zs2. zs2. zs2.
  lazymatch type of E2 with _ = (bt_upd _ _ _ _ _ ?hl2 _ _ _ _ _ _, _) => rewrite (srliw1 hl2) by lia; change (hl2 / 2 ^ 1) with (hl2 / 2) end.
  zs2. zs2. zs2. zstep.
  lazymatch type of E2 with _ = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) =>
    name_term R3 ER3 (build_tree_loop3 (Z.to_nat (hl2 / 2)) (bt_upd s t fc2 dl1 hp2 hl2 573 dp2 (ds_bl_count s) ol2 sl2 mc2) t (hl2 / 2));
    pose proof ER3 as ER3S; replace (Z.to_nat (hl2 / 2)) with (S (Z.to_nat (hl2 / 2) - 1)) in ER3S by lia end.
  lazymatch goal with HT : u8arr psegs ?mm T (u16s (avct ?fc2 ?dl1 N)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of E2 with _ = (bt_upd _ _ _ _ ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) =>
    call (bt_loop3 (Z.to_nat (hl2 / 2) - 1) L s t T N hl2 573 (hl2 / 2) fc2 dl1 hp2 dp2 (ds_bl_count s) ol2 sl2 mc2 R3 mm) end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. }
  1:{ eapply ct_readable_rw; [eassumption| lia| lia| cbn [disjoint_from]; lia]. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
  1:{ exact PQ2. } 1:{ exact RFC2. } 1:{ exact RDP2. } 1:{ lia. } 1:{ Z.div_mod_to_equations; lia. } 1:{ lia. } 1:{ exact ER3S. }
  match goal with H : R3 = bt_upd _ _ _ _ ?hp3 _ _ _ _ _ _ _ |- _ =>
    rename H into E3; clear ER3S; pose proof (av32_zlength hp3 573 ltac:(lia)) as L32_3 end.
  unfold l3R. zstep. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zstep.
  lazymatch type of E3 with R3 = ?X3 => name_term R4 ER4 (build_tree_loop4 573 X3 t (sd_elems t)) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of E3 with R3 = bt_upd _ _ ?fc2 ?dl1 ?hp3 ?hl2 _ ?dp2 _ ?ol2 ?sl2 ?mc2 =>
    call (bt_loop4 573 L s t T N hl2 573 (sd_elems t) dsc mc2 fc2 dl1 hp3 dp2 (ds_bl_count s) ol2 sl2 mc2 R4 mm) end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. }
  1:{ assumption. } 1:{ exact RFC2. } 1:{ exact RDP2. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ER4. }
  match goal with H : R4 = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ _ _ _ |- _ =>
    rename H into ER4'; pose proof ER4' as E4; rewrite ER4 in E4; clear ER4 ER4';
    pose proof (avct_zlength fc4 dl4 N ltac:(lia)) as LCT4; pose proof (av32_zlength hp4 573 ltac:(lia)) as L32_4; pose proof (av8_zlength dp4 573 ltac:(lia)) as L8_4 end.
  lazymatch type of E4 with _ = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ ?ol2 ?sl2 ?mc2 =>
    destruct (S7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E3 E4 ltac:(assumption) ltac:(lia)) as (RHP7 & RDL7 & OK1 & OK23 & LEN15) end.
  rewrite <- EN in RHP7, RDL7. clear S7.
  pose proof (sdesc_relro t _ (relro_clean_munch _ _ _ RC MU ltac:(cbn [disjoint_from]; unfold RELRO_LO, RELRO_HI; lia))) as Gsd. unfold sd_cells in Gsd.
  lazymatch type of E4 with _ = bt_upd _ _ _ _ _ 1 ?hm4 _ _ _ _ _ =>
    match goal with HG : rw_cells psegs _ (dl_As L + 5300) [C4 (wz 1); C4 (wz hm4)] |- _ =>
      replace (wz hm4) with (wz (hm4 - 1 + 1)) in HG by (f_equal; lia) end end.
  lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?rest) =>
    destruct (proj1 (rw_cells_app_iff mm A [c0] (c1 :: rest)) FR) as [F0 FR1]; clear FR;
    destruct (proj1 (rw_cells_app_iff mm _ [c1] rest) FR1) as [F1 F2]; clear FR1;
    cbn [cells_size csize Nat.add] in F1, F2 end.
  change (Z.of_nat 8) with 8 in F1. change (Z.of_nat 8) with 8 in F2. change (Z.of_nat 32) with 32 in F2.
  replace (bv_unsigned sp + -144 + 8) with (bv_unsigned sp + -136) in F1 by lia.
  replace (bv_unsigned sp + -144 + 8 + 32) with (bv_unsigned sp + -104) in F2 by lia.
  pose proof E3 as E3x. rewrite ER3 in E3x.
  rewrite (build_tree_flat s t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1 E2 E3x E4) in ER0.
  unfold l4R.
  lazymatch goal with HB : rw_cells psegs ?mm (bv_unsigned sp + -136) [CB 32 ?jk] |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of GD2 with rw_cells _ _ _ [CB 7 ?k0; _; _; _; _; CB 4 ?k1; _; _; _; _; _; CB 2 ?k2; _; CB 4 ?k3; _; _; CB 4 ?k4; _] =>
  lazymatch type of E4 with _ = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ ?ol2 ?sl2 ?mc2 =>
  lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (wz ?nd) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    call (partB L s t T N (hm4 - 1) nd dsc (SDA t) mc2 (STP t) (XP t) ol2 sl2 fc4 dl4 hp4 dp4 (ds_bl_count s) hh k0 k1 k2 k3 k4 jk R) end end end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact GD2. } 1:{ exact Gdsc. } 1:{ exact Gsd. }
  1:{ rewrite ESP. exact F0. } 1:{ rewrite ESP. replace (bv_unsigned sp + -144 + 8) with (bv_unsigned sp + -136) by lia. exact F1. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ lia. } 1:{ lia. } 1:{ exact EN. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact LBC. }
  1:{ apply xbits_view_of. } 1:{ apply stree_view_n_of. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Edsc. }
  1:{ lia. } 1:{ assumption. } 1:{ lia. } 1:{ exact RHP7. } 1:{ exact RDL7. } 1:{ assumption. } 1:{ lia. } 1:{ lia. }
  1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ exact OK1. } 1:{ exact OK23. } 1:{ exact LEN15. } 1:{ exact ER0. }
  rewrite ESP in *.
  do 13 zs2. zstep. zstep.
  release_frame F0 STK (bv_unsigned sp + -136).
  match goal with HF : rw_cells psegs _ (bv_unsigned sp + -144 + 8) [CB 32 _] |- _ =>
    replace (bv_unsigned sp + -144 + 8) with (bv_unsigned sp + -136) in HF by lia; release_frame HF STK (bv_unsigned sp + -104) end.
  release_frame F2 STK (bv_unsigned sp).
  match goal with HG : rw_cells psegs _ (dl_As L + 5881) (bD_cells _ _ ?ol ?sl ?k0 ?k1 ?k2 ?k3 ?k4), HR : R = bt_upd s t ?fc ?dl ?hp 1 ?hm ?dp ?bc _ _ ?mc |- _ =>
    apply evt_done; unfold body_post; do 15 eexists; exists fc, dl, hp, dp, bc, ol, sl, hm, mc, k0, k1, k2, k3, k4; eexists;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact STK|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact HG|];
    split; [eassumption|]; split; [exact HR|] end.
  repeat (split; [first [assumption | rewrite arr_len_set; assumption] |]). first [assumption | rewrite arr_len_set; assumption].
Qed.


Ltac bt_tree_lens LENS t :=
  lazymatch t with
  | TL => constr:(conj (ln_ltf _ LENS) (ln_ltd _ LENS))
  | TD => constr:(conj (ln_dtf _ LENS) (ln_dtd _ LENS))
  | TB => constr:(conj (ln_btf _ LENS) (ln_btd _ LENS))
  end.

Lemma dsB_cells_split : forall L s h1 h2 h3,
  dsB_cells L s h1 h2 h3
  = [C8 (wz (dl_As L + 212)); C4 (wz (ds_l_max_code s)); CB 4 h1; C8 (wz Z_SL_DESC)]
    ++ [C8 (wz (dl_As L + 2504)); C4 (wz (ds_d_max_code s)); CB 4 h2; C8 (wz Z_SD_DESC)]
    ++ [C8 (wz (dl_As L + 2748)); C4 (wz (ds_bl_max_code s)); CB 4 h3; C8 (wz Z_SBL_DESC)].
Proof. intros. reflexivity. Qed.

Lemma build_tree_spec : build_tree_stmt.
Proof.
  unfold build_tree_stmt. intros until m. intros ST MI RC STK LO AL BEL SAFE Ea0 Ea1.
  open_DST ST. pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0.
  destruct GB as (h1 & h2 & h3 & GB). destruct GD as (g0 & g1 & g2 & g3 & g4 & GD).
  rewrite dsB_cells_split in GB.
  destruct (proj1 (rw_cells_app_iff _ _ _ _) GB) as [GBl GB23]. destruct (proj1 (rw_cells_app_iff _ _ _ _) GB23) as [GBd GBb]. clear GB GB23.
  cbn [cells_size csize Nat.add] in GBd, GBb. change (Z.of_nat 24) with 24 in GBd, GBb.
  replace (dl_As L + 2904 + 24 + 24) with (dl_As L + 2952) in GBb by lia. replace (dl_As L + 2904 + 24) with (dl_As L + 2928) in GBd by lia.
  unfold dsC, dsC_cells in GC. change (dsD_cells L s g0 g1 g2 g3 g4) with (bD_cells L s (ds_opt_len s) (ds_static_len s) g0 g1 g2 g3 g4) in GD.
  unfold dblc, u16arr in Gblc. unfold dheap in Gheap. unfold ddep in Gdep.
  destruct t.
  -
    unfold dlt, u16arr in Glt.
    eapply evt_mono.
    { eapply (build_tree_body L s TL (dl_As L + 212) 573 (dl_As L + 2904) lo h1 g0 g1 g2 g3 g4 (build_tree s TL)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Glt. } 1:{ exact Gheap. } 1:{ exact Gdep. } 1:{ exact Gblc. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact GBl. }
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_BT_STACK in LO. exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_ltf _ LENS). } 1:{ exact (ln_ltd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBl' & ER & LFC' & LDL' & LHP' & LDP' & LBC').
    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport psegs W m m') in GBd; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport psegs W m m') in GBb; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
    unfold build_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite ER. constructor.
    + exact GA.
    + exists h1, h2, h3. rewrite dsB_cells_split.
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2928)); [exact GBl'| | cbn; lia].
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2952)); [exact GBd| exact GBb| cbn; lia].
    + exact GC'.
    + exists k0, k1, k2, k3, k4. exact GD'.
    + exact ARR'.
    + exact Gdt.
    + exact Gbt.
    + exact BLC'.
    + exact HPA'.
    + exact DPA'.
    + exact Gwin.
    + exact Gprev.
    + exact Ghead.
    + exact Gpend.
    + destruct LENS; constructor; cbn -[arr_len Z.add]; assumption.
    + exact LAY.
  -
    unfold ddt, u16arr in Gdt.
    eapply evt_mono.
    { eapply (build_tree_body L s TD (dl_As L + 2504) 61 (dl_As L + 2928) lo h2 g0 g1 g2 g3 g4 (build_tree s TD)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Gdt. } 1:{ exact Gheap. } 1:{ exact Gdep. } 1:{ exact Gblc. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact GBd. }
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_BT_STACK in LO. exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_dtf _ LENS). } 1:{ exact (ln_dtd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBd' & ER & LFC' & LDL' & LHP' & LDP' & LBC').
    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport psegs W m m') in GBl; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport psegs W m m') in GBb; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
    unfold build_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite ER. constructor.
    + exact GA.
    + exists h1, h2, h3. rewrite dsB_cells_split.
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2928)); [exact GBl| | cbn; lia].
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2952)); [exact GBd'| exact GBb| cbn; lia].
    + exact GC'.
    + exists k0, k1, k2, k3, k4. exact GD'.
    + exact Glt.
    + exact ARR'.
    + exact Gbt.
    + exact BLC'.
    + exact HPA'.
    + exact DPA'.
    + exact Gwin.
    + exact Gprev.
    + exact Ghead.
    + exact Gpend.
    + destruct LENS; constructor; cbn -[arr_len Z.add]; assumption.
    + exact LAY.
  -
    unfold dbt, u16arr in Gbt.
    eapply evt_mono.
    { eapply (build_tree_body L s TB (dl_As L + 2748) 39 (dl_As L + 2952) lo h3 g0 g1 g2 g3 g4 (build_tree s TB)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Gbt. } 1:{ exact Gheap. } 1:{ exact Gdep. } 1:{ exact Gblc. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact GBb. }
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_BT_STACK in LO. exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_btf _ LENS). } 1:{ exact (ln_btd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBb' & ER & LFC' & LDL' & LHP' & LDP' & LBC').
    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport psegs W m m') in GBl; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport psegs W m m') in GBd; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
    unfold build_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite ER. constructor.
    + exact GA.
    + exists h1, h2, h3. rewrite dsB_cells_split.
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2928)); [exact GBl| | cbn; lia].
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2952)); [exact GBd| exact GBb'| cbn; lia].
    + exact GC'.
    + exists k0, k1, k2, k3, k4. exact GD'.
    + exact Glt.
    + exact Gdt.
    + exact ARR'.
    + exact BLC'.
    + exact HPA'.
    + exact DPA'.
    + exact Gwin.
    + exact Gprev.
    + exact Ghead.
    + exact Gpend.
    + destruct LENS; constructor; cbn -[arr_len Z.add]; assumption.
    + exact LAY.
Qed.
End Z_tr_bt19.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_closed.Z_tr_bits OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb2.Z_tr_init OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_tr_fb11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_closed.Z_tr_bt19.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition tr_init_closed : tr_init_stmt := tr_init_spec.
Definition tr_flush_bits_closed : tr_flush_bits_stmt := tr_flush_bits_spec.
Definition tr_flush_block_closed : build_tree_stmt -> tr_flush_block_stmt := tr_flush_block_spec.

Theorem trees_closed : build_tree_stmt -> tr_init_stmt /\ tr_flush_bits_stmt /\ tr_flush_block_stmt.
Proof. intros BT. split; [exact tr_init_spec|]. split; [exact tr_flush_bits_spec| exact (tr_flush_block_spec BT)]. Qed.

Definition build_tree_closed : build_tree_stmt := build_tree_spec.
Definition tr_flush_block_final : tr_flush_block_stmt := tr_flush_block_closed build_tree_spec.
Theorem trees_closed_final : tr_init_stmt /\ tr_flush_bits_stmt /\ tr_flush_block_stmt.
Proof. exact (trees_closed build_tree_closed). Qed.
