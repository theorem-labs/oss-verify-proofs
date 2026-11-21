(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_scan1 Z_tr_scan2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees FillWinModel ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Ltac regs_eq tac :=
  f_equal; unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | (f_equal; tac)]
  | |- _ = _ => reflexivity
  end.

Definition sc_pre1_post (L : dlay) (s : deflate_state) (mc : Z)
    (ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a7 t3 m',
    ms' = MS (scR L (dl_As L + 212) mc (if arr_get (ds_dyn_ltree_dl s) 0 =? 0 then 138 else 7) (if arr_get (ds_dyn_ltree_dl s) 0 =? 0 then 3 else 4) 0
                  (arr_get (ds_dyn_ltree_dl s) 0) (dl_As L + 212 + 4 * 0 + 6) (-1) ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6)
             F (wz 0x1b210) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 212, dl_As L + 2504)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 212) (u16s (avct (ds_dyn_ltree_fc s) (arr_set (ds_dyn_ltree_dl s) (mc + 1) (wrap16 65535)) 573)).

Lemma sc_pre1 : forall (L : dlay) (s : deflate_state) (mc : Z) (hB1 hB2 hB3 : list byte)
    (ra sp gp tp t0 t1 t2 s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 212) (u16s (avct (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573)) -> arr_len (ds_dyn_ltree_dl s) = 573 ->
  rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) -> mem_inv psegs m -> dlay_ok L ->
  mc = ds_l_max_code s -> 0 <= mc -> mc + 1 < 573 -> 0 <= arr_get (ds_dyn_ltree_dl s) 0 < 65536 ->
  evt psegs (sc_pre1_post L s mc ra sp gp tp (wz (dl_As L)) s1r s2 s3 (wz (dl_As L + 2047)) s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (dl_As L + 2047)) s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b18c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LND GB MI LAY Emc Rmc Rmc2 Rnl.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. pose proof (avct_zlength (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ltac:(lia)) as LCT.
  unfold dsB_cells in GB. rewrite <- Emc in GB.
  pose proof (u16arr_read psegs m (dl_As L + 212) (avct (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573) (2 * 0 + 1) _ (wa (dl_As L + 212 + 2 * (2 * 0 + 1))) ARR
                (avct_nth_dl _ _ 573 0 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  set (nl := arr_get (ds_dyn_ltree_dl s) 0) in *.
  zs2. zs2. rewrite (zx16_small nl) by lia. zs2. shl_norm. zs2. zs2.
  ct_store_dl ARR (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 (dl_As L + 212) (mc + 1) (wrap16 65535) ltac:(apply le2_wz_mod; vm_compute; reflexivity).
  zstep. br_false.
  zs2. zs2. rewrite ?Z.mod_small by lia. zs2. zstep. br_cases K.
  -
    do 12 zs2.
    replace (0 <? nl) with false by (symmetry; apply Z.ltb_ge; lia). change (bv_swrap 32 (Z.b2z false + 3)) with 3.
    shl_norm. apply evt_done. unfold sc_pre1_post. fold nl. rewrite (proj2 (Z.eqb_eq nl 0) K). do 3 eexists.
    split; [unfold scR; regs_eq ltac:(lia)|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
  - do 13 zs2.
    replace (0 <? nl) with true by (symmetry; apply Z.ltb_lt; lia). change (bv_swrap 32 (Z.b2z true + 3)) with 4.
    shl_norm. apply evt_done. unfold sc_pre1_post. fold nl. rewrite (proj2 (Z.eqb_neq nl 0) K). do 3 eexists.
    split; [unfold scR; regs_eq ltac:(lia)|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
Qed.

Definition sc_pre2_post (L : dlay) (s : deflate_state) (mc : Z)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a7 t3 m',
    ms' = MS (scR2 L (dl_As L + 2504) mc (if arr_get (ds_dyn_dtree_dl s) 0 =? 0 then 138 else 7) (if arr_get (ds_dyn_dtree_dl s) 0 =? 0 then 3 else 4) 0
                   (arr_get (ds_dyn_dtree_dl s) 0) (dl_As L + 2504 + 4 * 0 + 6) (-1) t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6)
             F (wz 0x1b344) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 2504, dl_As L + 2748)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2504) (u16s (avct (ds_dyn_dtree_fc s) (arr_set (ds_dyn_dtree_dl s) (mc + 1) (wrap16 65535)) 61)).

Lemma sc_pre2 : forall (L : dlay) (s : deflate_state) (mc : Z) (hB1 hB2 hB3 : list byte)
    (ra sp gp tp t0 t1 t2 s1r a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2504) (u16s (avct (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) 61)) -> arr_len (ds_dyn_dtree_dl s) = 61 ->
  rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) -> mem_inv psegs m -> dlay_ok L ->
  mc = ds_d_max_code s -> 0 <= mc -> mc + 1 < 61 -> 0 <= arr_get (ds_dyn_dtree_dl s) 0 < 65536 ->
  evt psegs (sc_pre2_post L s mc t4 ra sp gp tp (wz (dl_As L)) s1r s2 s3 (wz (dl_As L + 2047)) s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1r (wz (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (dl_As L + 2047)) s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b2c8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LND GB MI LAY Emc Rmc Rmc2 Rnl.
  pose proof (munch_refl [(dl_As L + 2504, dl_As L + 2748)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. pose proof (avct_zlength (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) 61 ltac:(lia)) as LCT.
  unfold dsB_cells in GB. rewrite <- Emc in GB.
  pose proof (u16arr_read psegs m (dl_As L + 2504) (avct (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) 61) (2 * 0 + 1) _ (wa (dl_As L + 2504 + 2 * (2 * 0 + 1))) ARR
                (avct_nth_dl _ _ 61 0 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  set (nl := arr_get (ds_dyn_dtree_dl s) 0) in *.
  zs2. zs2. shl_norm. zs2. rewrite (zx16_small nl) by lia. zs2. zs2.
  ct_store_dl ARR (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) 61 (dl_As L + 2504) (mc + 1) (wrap16 65535) ltac:(apply le2_wz_mod; vm_compute; reflexivity).
  zstep. br_false.
  zs2. zs2. rewrite ?Z.mod_small by lia. zs2. zstep. br_cases K.
  -
    do 13 zs2.
    replace (0 <? nl) with false by (symmetry; apply Z.ltb_ge; lia). change (bv_swrap 32 (Z.b2z false + 3)) with 3.
    shl_norm. apply evt_done. unfold sc_pre2_post. fold nl. rewrite (proj2 (Z.eqb_eq nl 0) K). do 3 eexists.
    split; [unfold scR2; regs_eq ltac:(lia)|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
  - do 14 zs2.
    replace (0 <? nl) with true by (symmetry; apply Z.ltb_lt; lia). change (bv_swrap 32 (Z.b2z true + 3)) with 4.
    shl_norm. apply evt_done. unfold sc_pre2_post. fold nl. rewrite (proj2 (Z.eqb_neq nl 0) K). do 3 eexists.
    split; [unfold scR2; regs_eq ltac:(lia)|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
Qed.

Lemma guard_dl_facts : forall (dl : arr) N mc, arr_len dl = N -> 0 <= mc -> mc + 1 < N ->
  (forall i, 0 <= i < N -> 0 <= arr_get dl i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dl i <= 15) ->
  (forall i, 0 <= i < N -> 0 <= arr_get (arr_set dl (mc + 1) (wrap16 65535)) i < 65536)
  /\ (forall i, 0 <= i <= mc -> 0 <= arr_get (arr_set dl (mc + 1) (wrap16 65535)) i <= 15)
  /\ arr_get (arr_set dl (mc + 1) (wrap16 65535)) 0 = arr_get dl 0.
Proof.
  intros dl N mc LN H0 H1 HA HB.
  assert (G : forall i, arr_get (arr_set dl (mc + 1) (wrap16 65535)) i = if mc + 1 =? i then 65535 else arr_get dl i).
  { intros i. rewrite arr_get_set. unfold arr_inb. rewrite LN. destruct (Z.eqb_spec (mc + 1) i); cbn [andb]; [|reflexivity].
    rewrite (proj2 (Z.leb_le 0 (mc + 1))), (proj2 (Z.ltb_lt (mc + 1) N)) by lia. reflexivity. }
  split; [|split].
  - intros i Hi. rewrite G. destruct (mc + 1 =? i); [lia| apply HA; lia].
  - intros i Hi. rewrite G. destruct (Z.eqb_spec (mc + 1) i); [lia| apply HB; lia].
  - rewrite G. destruct (Z.eqb_spec (mc + 1) 0); [lia| reflexivity].
Qed.

Definition tfb_scan1_post (L : dlay) (s : deflate_state)
    (ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists vt0 vt1 vt2 va1 va3 vt4 a7 t3 m',
    ms' = MS (scR L (dl_As L + 212) (ds_l_max_code s) vt0 vt1 vt2 va1 va3 vt4 ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b2c8) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 212, dl_As L + 2504); (dl_As L + 2748, dl_As L + 2904)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ dlt m' L (scan_tree s TL (ds_l_max_code s)) /\ dbt m' L (scan_tree s TL (ds_l_max_code s)).

Lemma tfb_scan1 : forall (L : dlay) (s : deflate_state) (hB1 hB2 hB3 : list byte)
    (ra sp gp tp t0 t1 t2 s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dlt m L s -> dbt m L s -> rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  arr_len (ds_dyn_ltree_dl s) = 573 -> arr_len (ds_bl_tree_fc s) = 39 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_l_max_code s -> ds_l_max_code s + 1 < 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_dl s) i < 65536) -> (forall i, 0 <= i <= ds_l_max_code s -> 0 <= arr_get (ds_dyn_ltree_dl s) i <= 15) ->
  evt psegs (tfb_scan1_post L s ra sp gp tp (wz (dl_As L)) s1r s2 s3 (wz (dl_As L + 2047)) s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (dl_As L + 2047)) s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b18c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Glt Gbt GB LND LNB MI LAY Rmc1 Rmc2 HDL HLEN.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504); (dl_As L + 2748, dl_As L + 2904)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof LAY as LAY'. lay_open LAY'.
  unfold dlt, u16arr in Glt. unfold dbt, u16arr in Gbt.
  pose proof (avct_zlength (ds_bl_tree_fc s) (ds_bl_tree_dl s) 39 ltac:(lia)) as LCTb.
  remember (ds_l_max_code s) as mc eqn:Emc.
  destruct (guard_dl_facts (ds_dyn_ltree_dl s) 573 mc LND Rmc1 Rmc2 HDL HLEN) as (HDL' & HLEN' & E0).
  call (sc_pre1 L s mc hB1 hB2 hB3).
  1:{ exact Glt. } 1:{ exact LND. } 1:{ exact GB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Emc. } 1:{ exact Rmc1. } 1:{ exact Rmc2. } 1:{ apply HDL. lia. }
  set (nl := arr_get (ds_dyn_ltree_dl s) 0) in *.
  set (dlT := arr_set (ds_dyn_ltree_dl s) (mc + 1) (wrap16 65535)) in *.
  set (s1 := set_Len s TL (mc + 1) 65535).
  pose proof (avct_zlength (ds_dyn_ltree_fc s) dlT 573 ltac:(lia)) as LCTl.
  remember (scan_tree s TL mc) as R eqn:ER.
  destruct (Z.to_nat (mc + 1)) as [|f] eqn:Ef; [lia|].
  assert (ER' : R = scan_tree_loop (S f) (set_bl_tree_fc s1 (ds_bl_tree_fc s)) TL mc 0 (-1) nl 0 (if nl =? 0 then 138 else 7) (if nl =? 0 then 3 else 4)).
  { rewrite ER. unfold scan_tree. change (Len s TL 0) with nl. rewrite Ef. change (set_Len s TL (mc + 1) 65535) with s1.
    change (ds_bl_tree_fc s) with (ds_bl_tree_fc s1). rewrite (sbf_self s1). destruct (nl =? 0); reflexivity. }
  match goal with H : u8arr _ ?mc0 (dl_As L + 212) _ |- evt _ _ (MS _ _ _ _ _ ?mc0 _) =>
    pose proof (ct_readable_rw (Wbt L) mc0 (dl_As L + 212) (ds_dyn_ltree_fc s) dlT 573 573 H ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; lia)) as RDT;
    call (sc_loop f L s1 TL (dl_As L + 212) 573 mc (ds_dyn_ltree_fc s) dlT (ds_bl_tree_dl s) R mc0 0 (ds_bl_tree_fc s) (-1) nl 0 (if nl =? 0 then 138 else 7) (if nl =? 0 then 3 else 4))
  end.
  1:{ eassumption. } 1:{ exact LNB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RDT. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ intros i. reflexivity. } 1:{ exact HDL'. } 1:{ exact HLEN'. } 1:{ lia. } 1:{ subst dlT. rewrite E0. reflexivity. }
  1:{ destruct (nl =? 0); lia. } 1:{ destruct (nl =? 0); auto. } 1:{ destruct (nl =? 0); auto. } 1:{ lia. } 1:{ lia. } 1:{ exact ER'. }
  subst dlT s1. subst mc. apply evt_done. unfold tfb_scan1_post. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  rewrite <- ER. match goal with E : R = set_bl_tree_fc _ _ |- _ => rewrite E end.
  split; [unfold dlt, u16arr; match goal with H : u8arr _ _ (dl_As L + 212) _ |- _ => exact H end
         | unfold dbt, u16arr; match goal with H : u8arr _ _ (dl_As L + 2748) _ |- _ => exact H end].
Qed.

Definition tfb_scan2_post (L : dlay) (s : deflate_state)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists vt0 vt1 vt2 va1 va3 vt4 a7 t3 m',
    ms' = MS (scR2 L (dl_As L + 2504) (ds_d_max_code s) vt0 vt1 vt2 va1 va3 vt4 t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b3fc) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L + 2504, dl_As L + 2748); (dl_As L + 2748, dl_As L + 2904)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ ddt m' L (scan_tree s TD (ds_d_max_code s)) /\ dbt m' L (scan_tree s TD (ds_d_max_code s)).

Lemma tfb_scan2 : forall (L : dlay) (s : deflate_state) (hB1 hB2 hB3 : list byte)
    (ra sp gp tp t0 t1 t2 s1r a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  ddt m L s -> dbt m L s -> rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  arr_len (ds_dyn_dtree_dl s) = 61 -> arr_len (ds_bl_tree_fc s) = 39 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_d_max_code s -> ds_d_max_code s + 1 < 61 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_dl s) i < 65536) -> (forall i, 0 <= i <= ds_d_max_code s -> 0 <= arr_get (ds_dyn_dtree_dl s) i <= 15) ->
  evt psegs (tfb_scan2_post L s t4 ra sp gp tp (wz (dl_As L)) s1r s2 s3 (wz (dl_As L + 2047)) s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L)) s1r (wz (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz (dl_As L + 2047)) s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b2c8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros Gdt Gbt GB LND LNB MI LAY Rmc1 Rmc2 HDL HLEN.
  pose proof (munch_refl [(dl_As L + 2504, dl_As L + 2748); (dl_As L + 2748, dl_As L + 2904)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof LAY as LAY'. lay_open LAY'.
  unfold ddt, u16arr in Gdt. unfold dbt, u16arr in Gbt.
  pose proof (avct_zlength (ds_bl_tree_fc s) (ds_bl_tree_dl s) 39 ltac:(lia)) as LCTb.
  remember (ds_d_max_code s) as mc eqn:Emc.
  destruct (guard_dl_facts (ds_dyn_dtree_dl s) 61 mc LND Rmc1 Rmc2 HDL HLEN) as (HDL' & HLEN' & E0).
  call (sc_pre2 L s mc hB1 hB2 hB3).
  1:{ exact Gdt. } 1:{ exact LND. } 1:{ exact GB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Emc. } 1:{ exact Rmc1. } 1:{ exact Rmc2. } 1:{ apply HDL. lia. }
  set (nl := arr_get (ds_dyn_dtree_dl s) 0) in *.
  set (dlT := arr_set (ds_dyn_dtree_dl s) (mc + 1) (wrap16 65535)) in *.
  set (s1 := set_Len s TD (mc + 1) 65535).
  pose proof (avct_zlength (ds_dyn_dtree_fc s) dlT 61 ltac:(lia)) as LCTl.
  remember (scan_tree s TD mc) as R eqn:ER.
  destruct (Z.to_nat (mc + 1)) as [|f] eqn:Ef; [lia|].
  assert (ER' : R = scan_tree_loop (S f) (set_bl_tree_fc s1 (ds_bl_tree_fc s)) TD mc 0 (-1) nl 0 (if nl =? 0 then 138 else 7) (if nl =? 0 then 3 else 4)).
  { rewrite ER. unfold scan_tree. change (Len s TD 0) with nl. rewrite Ef. change (set_Len s TD (mc + 1) 65535) with s1.
    change (ds_bl_tree_fc s) with (ds_bl_tree_fc s1). rewrite (sbf_self s1). destruct (nl =? 0); reflexivity. }
  match goal with H : u8arr _ ?mc0 (dl_As L + 2504) _ |- evt _ _ (MS _ _ _ _ _ ?mc0 _) =>
    pose proof (ct_readable_rw (Wbt L) mc0 (dl_As L + 2504) (ds_dyn_dtree_fc s) dlT 61 61 H ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; lia)) as RDT;
    call (sd_loop f L s1 TD (dl_As L + 2504) 61 mc (ds_dyn_dtree_fc s) dlT (ds_bl_tree_dl s) R mc0 0 (ds_bl_tree_fc s) (-1) nl 0 (if nl =? 0 then 138 else 7) (if nl =? 0 then 3 else 4))
  end.
  1:{ eassumption. } 1:{ exact LNB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RDT. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ intros i. reflexivity. } 1:{ exact HDL'. } 1:{ exact HLEN'. } 1:{ lia. } 1:{ subst dlT. rewrite E0. reflexivity. }
  1:{ destruct (nl =? 0); lia. } 1:{ destruct (nl =? 0); auto. } 1:{ destruct (nl =? 0); auto. } 1:{ lia. } 1:{ lia. } 1:{ exact ER'. }
  subst dlT s1. subst mc. apply evt_done. unfold tfb_scan2_post. do 9 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  rewrite <- ER. match goal with E : R = set_bl_tree_fc _ _ |- _ => rewrite E end.
  split; [unfold ddt, u16arr; match goal with H : u8arr _ _ (dl_As L + 2504) _ |- _ => exact H end
         | unfold dbt, u16arr; match goal with H : u8arr _ _ (dl_As L + 2748) _ |- _ => exact H end].
Qed.
