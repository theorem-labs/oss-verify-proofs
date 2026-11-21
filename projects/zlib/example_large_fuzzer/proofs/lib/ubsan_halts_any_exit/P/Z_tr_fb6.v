(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_st4 Z_tr_st13 Z_tr_fb1 Z_tr_fb4 Z_tr_fb5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab RefFlushBlk12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma tfb_dyn_hdr2 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV0 BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a0 a3 a4 a6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wcell (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= mb <= 18 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bdl i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (bl_calls s 0 (Z.to_nat (mb + 1))) ->
  R = sbs_run (upd4 s PB PD BB BV) (bl_calls s 0 (Z.to_nat (mb + 1))) ->
  evt psegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 a0 w (wz (ds_l_max_code s)) a3 a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1ba90) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Ebdl EMH HW MI LAY MU WM RDB Rmb RBd RBV RPD HSB ER. unfold tfR.
  pose proof EMH as EMo. lay_open LAY. open_EM EMo.
  zs2. do 7 zs2.
  destruct (Z.to_nat (mb + 1)) as [|k] eqn:En; [lia|].
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (EM1 : EM mm L s PB PD wcell (wz BV)) by close_EM GA GD Gpend end.
  clear GA GD Gpend.
  replace (wz 74816) with (wz (Z_BL_ORDER + 0)) by reflexivity. change (74816 + (mb + 1)) with (Z_BL_ORDER + (mb + 1)).
  eapply (tfb_blo_loop k L s bfc bdl sp last bufp mb 0 R m0 PB PD BB BV wcell w);
    [exact Ebdl| exact EM1| exact HW| eassumption| assumption| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV| exact RPD| exact HSB| exact ER].
Qed.

Lemma tfb_dyn_hdr : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last len bufp mb : Z) (R : deflate_state)
    (PB : arr) (PD BB BV : Z) (wbb : word) (hB1 hB2 hB3 : list byte)
    (ra gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= last <= 1 -> 0 <= ds_l_max_code s < 2^31 -> 0 <= ds_d_max_code s < 2^31 -> 0 <= mb <= 18 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bdl i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (hd_calls last s mb) ->
  R = sbs_run (upd4 s PB PD BB BV) (hd_calls last s mb) ->
  evt psegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 (wz BV) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b838) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Ebdl EMH HBB MI LAY GB RDB Rl Rlm Rdm Rmb RBd RBV RPD HSB ER.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (lo_sb _ LAY) as SEPsb. unfold apart in SEPsb. pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & Rb & _).
  unfold dsB_cells in GB. unfold hd_calls in HSB, ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM1 & HSB). rewrite sbs_run_cons_flat in ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM2 & HSB). rewrite sbs_run_cons_flat in ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM3 & HSB). rewrite sbs_run_cons_flat in ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM4 & HSB). rewrite sbs_run_cons_flat in ER.
  pose proof (sbF_BV_range BV 3 RBV ltac:(lia)) as RBV1. pose proof (sbF_BV_range _ 5 RBV1 ltac:(lia)) as RBV2.
  pose proof (sbF_BV_range _ 5 RBV2 ltac:(lia)) as RBV3. pose proof (sbF_BV_range _ 4 RBV3 ltac:(lia)) as RBV4.
  assert (RPD1 : 0 <= sbF_PD PD BV 3) by (apply sbF_PD_nonneg; exact RPD).
  assert (RPD2 : 0 <= sbF_PD (sbF_PD PD BV 3) (sbF_BV BV 3) 5) by (apply sbF_PD_nonneg; exact RPD1).
  assert (RPD3 : 0 <= sbF_PD (sbF_PD (sbF_PD PD BV 3) (sbF_BV BV 3) 5) (sbF_BV (sbF_BV BV 3) 5) 5) by (apply sbF_PD_nonneg; exact RPD2).
  assert (RPD4 : 0 <= sbF_PD (sbF_PD (sbF_PD (sbF_PD PD BV 3) (sbF_BV BV 3) 5) (sbF_BV (sbF_BV BV 3) 5) 5) (sbF_BV (sbF_BV (sbF_BV BV 3) 5) 5) 4) by (apply sbF_PD_nonneg; exact RPD3).
  call (tfb_d1 L s sp last len bufp mb PB PD BB BV wbb).
  1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM1; lia. }
  match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (tfb_d2 L s sp last len bufp mb pb pd bb bv0 (sbF_BV BV 3) wc wr hB1 hB2 hB3);
    [exact H| exact HB| eassumption| exact LAY| exact GB| exact Rlm| exact Rdm| exact RBV1| lia| intros; apply ROOM2; lia|] end.
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X2]|[-> X2]] end.
  -
    match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (tfb_d3k L s sp last bufp mb pb pd bb bv wc wr);
      [exact H| exact HB| eassumption| exact LAY| exact Rdm| lia| lia| exact Rmb|] end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X3]|[-> X3]] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4k L s sp last bufp mb pb pd bb bv wc wr);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| exact Rmb|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 _ wc wr);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| exact Rmb| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4f L s sp last bufp mb pb pd bb bv wc wr);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| apply ROOM4; lia| exact Rmb|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 _ wc wr);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| exact Rmb| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
  -
    match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (tfb_d3f L s sp last bufp mb pb pd bb bv wc wr);
      [exact H| exact HB| eassumption| exact LAY| exact Rdm| lia| lia| apply ROOM3; lia| exact Rmb|] end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X3]|[-> X3]] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4k L s sp last bufp mb pb pd bb bv wc wr);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| exact Rmb|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 _ wc wr);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| exact Rmb| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4f L s sp last bufp mb pb pd bb bv wc wr);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| apply ROOM4; lia| exact Rmb|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wr mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 _ wc wr);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| exact Rmb| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
Qed.
