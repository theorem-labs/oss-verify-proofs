(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_model Z_slow_kit Z_tr_kit Z_fw_model Z_fw_kit Zg_fw_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_FW_INSL : Z := 0x16a48.
Definition Z_FW_LOOPT : Z := 0x16ab4.

Definition il_h (s : deflate_state) (str : Z) : Z := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + 2)).
Definition il_next (s : deflate_state) (str : Z) : deflate_state :=
  set_insert (set_head (set_prev (set_ins_h s (il_h s str)) (arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) (il_h s str))))
                       (arr_set (ds_head s) (il_h s str) (wrap16 str))) (ds_insert s - 1).

Lemma fill_window_insert_next : forall s str, ds_insert s <> 0 -> 1 <= ds_insert s ->
  fill_window_insert (Z.to_nat (ds_insert s)) s str
  = (if ds_lookahead s + (ds_insert s - 1) <? 3 then il_next s str else fill_window_insert (Z.to_nat (ds_insert (il_next s str))) (il_next s str) (str + 1)).
Proof.
  intros s str Hnz H1. rewrite (fill_window_insert_step (ds_insert s) s str H1).
  replace (ds_insert s =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). cbn [negb]. cbv zeta. unfold il_next, il_h, MIN_MATCH. dsred.
  change (3 - 1) with 2. reflexivity.
Qed.

Lemma fill_window_insert_shape : forall n s str, exists pv hd ih ins,
  fill_window_insert n s str = set_insert (set_head (set_prev (set_ins_h s ih) pv) hd) ins
  /\ arr_len pv = arr_len (ds_prev s) /\ arr_len hd = arr_len (ds_head s).
Proof.
  induction n as [|n IH]; intros s str.
  - exists (ds_prev s), (ds_head s), (ds_ins_h s), (ds_insert s). split; [destruct s; reflexivity| split; reflexivity].
  - cbn [fill_window_insert]. destruct (negb (ds_insert s =? 0)).
    2:{ exists (ds_prev s), (ds_head s), (ds_ins_h s), (ds_insert s). split; [destruct s; reflexivity| split; reflexivity]. }
    cbv zeta. dsred. destruct (_ <? MIN_MATCH).
    + do 4 eexists. split; [reflexivity|]. rewrite !arr_len_set. split; reflexivity.
    + lazymatch goal with |- exists pv hd ih ins, fill_window_insert n ?s4 ?str4 = _ /\ _ =>
        destruct (IH s4 str4) as (pv & hd & ih & ins & E & Lp & Lh); rewrite E; exists pv, hd, ih, ins end.
      revert Lp Lh. dsred. rewrite !arr_len_set. intros Lp Lh. split; [destruct s; reflexivity| split; [exact Lp| exact Lh]].
Qed.

Lemma le2_sx16 : forall v, 0 <= v < 65536 -> le2 (sx16 (wz v)) = le2 (wz v).
Proof.
  intros v Hv. apply le2_wz_mod. unfold sx16. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul N.sub N.of_nat Pos.of_succ_nat].
  Z.div_mod_to_equations. lia.
Qed.

Section INSL.
Variables (L : dlay) (r : sregs) (F : bvmap 5 word) (fc : bv 32).
Variables (hA1 hA2 hA3 hA4 hA5 hD0 hD1 hD2 hD3 hD4 : list byte).
Variables (y1 y9 y18 y19 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 : word).

Definition il_post (look : Z) (s' : deflate_state) (m : mem) : machine_state -> Prop :=
  fun ms' => exists v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 m',
    ms' = MS (mkR y1 (wz (bv_unsigned (r_sp r) + -112)) (r_gp r) (r_tp r) v5 v6 v7 (wz (dl_As L)) y9 (wz look) v11 v12 v13 v14 v15 v16 v17 y18 y19
                  (wz (dl_As L + 5932)) y21 y22 (wz 2) y24 y25 y26 y27 y28 y29 y30 y31)
             F (wz Z_FW_LOOPT) fc None m' (seg_rom psegs)
    /\ munch [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' (dl_As L) (dsA_cells L s' hA1 hA2 hA3 hA4 hA5)
    /\ rw_cells psegs m' (dl_As L + 5881) (dsD_cells L s' hD0 hD1 hD2 hD3 hD4)
    /\ u8arr psegs m' (dl_Ap L) (u16s (av16 (ds_prev s') 32768))
    /\ u8arr psegs m' (dl_Ah L) (u16s (av16 (ds_head s') 32768)).

Hypothesis LAY : dlay_ok L.

Lemma fw_insloop : forall (k : nat) (s : deflate_state) (str : Z) (y5 y6 y7 y17 : word) (m : mem),
  ds_insert s = Z.of_nat k ->
  fw_wf 32768 32768 s -> 0 <= str -> ds_insert s = ds_strstart s - str -> (ds_insert s <> 0 -> 3 <= ds_lookahead s + ds_insert s) ->
  rw_cells psegs m (dl_As L) (dsA_cells L s hA1 hA2 hA3 hA4 hA5) ->
  rw_cells psegs m (dl_As L + 5881) (dsD_cells L s hD0 hD1 hD2 hD3 hD4) ->
  u8arr psegs m (dl_Aw L) (av8 (ds_window s) 65536) ->
  u8arr psegs m (dl_Ap L) (u16s (av16 (ds_prev s) 32768)) ->
  u8arr psegs m (dl_Ah L) (u16s (av16 (ds_head s) 32768)) ->
  mem_inv psegs m ->
  evt psegs (il_post (ds_lookahead s) (fill_window_insert (Z.to_nat (ds_insert s)) s str) m)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -112)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 (wz (ds_lookahead s)) (wz (ds_insert s))
             (wz (ds_hash_shift s)) (wz (dl_Aw L)) (wz (ds_hash_mask s)) (wz str) (wz (ds_ins_h s)) y17 y18 y19
             (wz (dl_As L + 5932)) y21 y22 (wz 2) y24 y25 y26 y27 y28 y29 y30 y31)
        F (wz Z_FW_INSL) fc None m (seg_rom psegs)).
Proof.
  induction k as [|k IH]; intros s str y5 y6 y7 y17 m Hk FW Hstr Hins Hbig GA GD Gwin Gprev Ghead MI; unfold Z_FW_INSL.
  -
    pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] m) as MU0.
    pose proof (wmono_refl psegs m) as WM0.
    rewrite Hk. change (Z.to_nat (Z.of_nat 0)) with 0%nat. cbn [fill_window_insert].
    zstep. br_true.
    apply evt_done. unfold il_post, Z_FW_LOOPT. do 10 eexists. exists m.
    split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [exact MI|].
    split; [exact GA|]. split; [exact GD|]. split; [exact Gprev| exact Ghead].
  -
    pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] m) as MU0.
    pose proof (wmono_refl psegs m) as WM0.
    lay_open LAY.
    pose proof FW as FW0. destruct FW as [Wws Wwsr Wwl Wwsz Wpl Wwm Whs Whsr Whl Whm Whsh Wins Wlook Wsl Wms Wih Whw Wni Wai Winl Wti Wwr Wad1 Wad2 Wwb Wpb Whb Wib].
    specialize (Hbig ltac:(lia)).
    unfold dsA_cells in GA. unfold dsD_cells in GD.
    pose proof (av16_zlength (ds_prev s) 32768 ltac:(lia)) as L16p. pose proof (av16_zlength (ds_head s) 32768 ltac:(lia)) as L16h.
    pose proof (av8_zlength (ds_window s) 65536 ltac:(lia)) as LW.
    rewrite (fill_window_insert_next s str) by lia.
    zstep. br_false.
    zs. zs. zs. zs. zs. zs. zs. rewrite ?Z.mod_small by lia. zs.
    ld8 Gwin (ds_window s) 65536 (dl_Aw L) (str + 2) ltac:(apply Wwb; lia).
    zs. zs. zs. zs. zs.
    replace (Z.land (Z.lxor (bv_swrap 32 (Z.shiftl (ds_ins_h s) (ds_hash_shift s)) mod 18446744073709551616) (arr_get (ds_window s) (str + 2) mod 18446744073709551616)) (ds_hash_mask s))
      with (il_h s str).
    2:{ unfold il_h. rewrite <- (hash_mach s (ds_ins_h s) (arr_get (ds_window s) (str + 2))) by lia. rewrite (Z.mod_small (ds_hash_shift s) 32) by lia. reflexivity. }
    pose proof (update_hash_range s (ds_ins_h s) (arr_get (ds_window s) (str + 2)) ltac:(lia)) as Rhv. change (update_hash _ _ _) with (il_h s str) in Rhv.
    remember (il_h s str) as h eqn:Eh.
    rewrite (Z.shiftl_mul_pow2 (Z.land str (ds_w_mask s)) 1) by lia. change (2^1) with 2. rewrite (Z.mul_comm (Z.land str (ds_w_mask s)) 2).
    pose proof (land_upper_both str (ds_w_mask s) ltac:(lia) ltac:(lia)) as Rpi.
    remember (Z.land str (ds_w_mask s)) as pi eqn:Epi.
    zs. zs. rewrite (shl32_shr31 h) by lia. zs.
    pose proof (u16arr_read psegs _ (dl_Ah L) (av16 (ds_head s) 32768) h (wz (arr_get (ds_head s) h)) (wa (dl_Ah L + 2 * h)) Ghead (av16_nth (ds_head s) 32768 h ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. clear RD. pose proof (Whb h ltac:(lia)) as Rhh.
    zs. zs.
    zs.
    st16 Gprev (ds_prev s) 32768 (dl_Ap L) pi (arr_get (ds_head s) h) ltac:(apply le2_sx16; exact Rhh).
    st16 Ghead (ds_head s) 32768 (dl_Ah L) h (wrap16 str) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
    zs. zs.
    name_mem m1.
    zstep. br_cases K.
    +
      replace (ds_lookahead s + (ds_insert s - 1) <? 3) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      replace (wz (ds_insert s + -1)) with (wz (ds_insert (il_next s str))) by (unfold il_next; dsred; f_equal; lia).
      replace (wz h) with (wz (ds_ins_h (il_next s str))) by (unfold il_next; dsred; rewrite Eh; reflexivity).
      change (wz (ds_lookahead s)) with (wz (ds_lookahead (il_next s str))).
      change (wz (ds_hash_shift s)) with (wz (ds_hash_shift (il_next s str))).
      change (wz (ds_hash_mask s)) with (wz (ds_hash_mask (il_next s str))).
      eapply evt_mono.
      * eapply (IH (il_next s str) (str + 1)).
        -- unfold il_next. dsred. lia.
        -- unfold il_next. rewrite <- Eh, <- Epi. destruct FW0; constructor; dsred; try assumption; try lia;
             first [ rewrite arr_len_set; assumption
                   | intros i Hi; rewrite arr_get_set; destruct (_ && _); first [apply wrap16_range| apply Whb; lia| apply Wpb; lia] ].
        -- lia.
        -- unfold il_next. dsred. lia.
        -- unfold il_next. dsred. lia.
        -- unfold dsA_cells, il_next. dsred. rewrite <- Eh. close_cells GA.
        -- unfold dsD_cells, il_next. dsred. close_cells GD.
        -- unfold il_next. dsred. exact Gwin.
        -- unfold il_next. dsred. rewrite <- Eh, <- Epi. exact Gprev.
        -- unfold il_next. dsred. rewrite <- Eh. exact Ghead.
        -- assumption.
      * intros ms' (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & m2 & -> & MU2 & WM2 & MI2 & GA2 & GD2 & P2 & H2).
        unfold il_post. exists v5, v6, v7, v11, v12, v13, v14, v15, v16, v17, m2.
        split; [reflexivity|]. split; [eapply munch_trans; [exact MU0| exact MU2]|]. split; [eapply wmono_trans; [exact WM0| exact WM2]|].
        split; [exact MI2|]. split; [exact GA2|]. split; [exact GD2|]. split; [exact P2| exact H2].
    +
      replace (ds_lookahead s + (ds_insert s - 1) <? 3) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      apply evt_done. unfold il_post, Z_FW_LOOPT. do 10 eexists. exists m1.
      split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [assumption|].
      split; [unfold dsA_cells, il_next; dsred; rewrite <- Eh; close_cells GA|].
      split; [unfold dsD_cells, il_next; dsred; close_cells GD|].
      split; [unfold il_next; dsred; rewrite <- Eh, <- Epi; exact Gprev| unfold il_next; dsred; rewrite <- Eh; exact Ghead].
Qed.
End INSL.
