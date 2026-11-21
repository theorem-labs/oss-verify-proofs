(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_tr_rod Zg_fast_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast2 RefDeflFast3 RefDeflFast6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma d_code_idxf : forall dd, d_code dd = arr_get dist_code_a (if dd <? 256 then dd else 256 + Z.shiftr dd 7).
Proof. intros dd. unfold d_code. destruct (dd <? 256); reflexivity. Qed.

Section FDIST2.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Definition KDEC (Q : machine_state -> Prop) (pc : Z) (T : deflate_state) (sn se : Z) : Prop :=
  forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me T m' ->
    evt psegs Q (MS (fastR L r y1 y5 y6 y7 (wz sn) (wz se) (wz (ds_match_length T)) y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31)
                    F (wz pc) fc None m' (seg_rom psegs)).

Lemma fast_tdist2 : forall (Q : machine_state -> Prop) (S : deflate_state) (dd w10 : Z)
    (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m : mem),
  FINV L flush rest0 lo r me S m ->
  Z.land (w10 mod 18446744073709551616) 65535 = dd -> 0 <= dd < 32768 ->
  0 <= ds_match_length S <= 258 -> 0 <= ds_lookahead S <= 65536 -> ds_match_length S <= ds_lookahead S -> 0 <= ds_max_lazy_match S < 2^31 ->
  0 <= ds_sym_next S < 2^18 -> 0 <= ds_sym_end S < 2^18 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc S) i < 65536) ->
  (ins_cond (tdist2 S (d_code dd)) = true -> KDEC Q 0x191ac (tdist2 S (d_code dd)) (ds_sym_next S) (ds_sym_end S)) ->
  (ins_cond (tdist2 S (d_code dd)) = false -> KDEC Q 0x19244 (tdist2 S (d_code dd)) (ds_sym_next S) (ds_sym_end S)) ->
  evt psegs Q (MS (fastR L r y1 y5 y6 y7 (wz w10) (wz dd) y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31)
                  F (wz 0x19158) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) EDD Rdd Rml Rla MLLA Rlazy Rsn Rse Rdfc KI KN.
  apply box in EDD.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_ct Gdt.
  pose proof (ln_dtf _ LENS) as Ldtf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR. unfold fast_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 2504, dl_As L + 2748)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  zs. zstep.
  eapply (evt_cut psegs (fun ms' => exists v11 : word, ms' =
     MS (mkR y1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz 261)
             (wz (if dd <? 256 then dd else 256 + Z.shiftr dd 7)) v11 (wz 256) y13 y14 y15 y16 y17 y18 y19
             (wz Z_LENGTH_CODE) (wz (-1)) (wz (dl_As L + 212)) (wz (dl_As L + 5888)) (wz Z_DIST_CODE) (wz (dl_As L + 2504)) (wz 3) (wz 65535) y28 y29 y30 y31)
        F (wz 0x1916c) fc None mA (seg_rom psegs))).
  { if_cases KDD; zify_cond KDD; rewrite ?unsigned_lit in KDD by lia.
    -
      zs. rewrite (unbox _ EDD).
      replace (wz dd) with (wz (if dd <? 256 then dd else 256 + Z.shiftr dd 7)) by (replace (dd <? 256) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      apply evt_done. eexists. reflexivity.
    - zs. zs. zs.
      replace (Z.land ((dd ≫ 7 + 256) mod 18446744073709551616) 65535) with (if dd <? 256 then dd else 256 + Z.shiftr dd 7).
      2:{ replace (dd <? 256) with false by (symmetry; apply Z.ltb_ge; lia).
          change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia.
          rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. change (2^64) with 18446744073709551616. change (2^16) with 65536.
          Z.div_mod_to_equations. lia. }
      apply evt_done. eexists. reflexivity. }
  intros ms' (v11 & ->).
  assert (Rdci : 0 <= (if dd <? 256 then dd else 256 + Z.shiftr dd 7) < 512).
  { destruct (Z.ltb_spec dd 256); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. Z.div_mod_to_equations. lia. }
  pose proof (d_code_idxf dd) as EDC.
  remember (if dd <? 256 then dd else 256 + Z.shiftr dd 7) as dci eqn:Edci. clear Edci.
  unfold Z_DIST_CODE.
  zs.
  pose proof (rod_dist_code _ MI) as TDC. unfold Z_DIST_CODE in TDC.
  ld8ro TDC dist_code_a 512 72432 dci dc Edc ltac:(pose proof (dist_code_range dci Rdci); lia).
  clear TDC. pose proof (dist_code_range dci Rdci) as Rdc30. rewrite <- Edc in Rdc30. rewrite <- EDC in Edc.
  (* 1.4: &dyn_dtree is in s9, no ld from the frame *)
  do 4 zs.
  replace (wz (dl_As L + 2504 + dc ≪ 2)) with (wz (dl_As L + 2504 + 4 * dc)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (u16arr_read psegs _ (dl_As L + 2504) (avct (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61) (2 * dc)
                (wz (arr_get (ds_dyn_dtree_fc S) dc)) (wa (dl_As L + 2504 + 4 * dc)) Gdt
                (avct_nth_fc _ _ 61 dc ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD.
  zs. zs. zs. zs.
  ct_store_fc Gdt (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61 (dl_As L + 2504) dc (wrap16 (arr_get (ds_dyn_dtree_fc S) dc + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rdfc; lia).
  zs. zs. name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : FINV L flush rest0 lo r me (tdist2 S (d_code dd)) mB).
  { subst dc. split; [split|].
    - exact ZS.
    - unfold tdist2. constructor;
        [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| do 5 eexists; exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  unfold ins_cond, MIN_MATCH in KI, KN. unfold KDEC, fastR in KI, KN.
  replace (ds_match_length (tdist2 S (d_code dd))) with (ds_match_length S) in KI, KN by reflexivity.
  replace (ds_max_lazy_match (tdist2 S (d_code dd))) with (ds_max_lazy_match S) in KI, KN by reflexivity.
  replace (ds_lookahead (tdist2 S (d_code dd))) with (ds_lookahead S - ds_match_length S) in KI, KN by reflexivity.
  zstep. if_cases KC1; zify_cond KC1; rewrite ?unsigned_lit in KC1 by lia.
  -
    eapply KN; [| exact SI'].
    replace (ds_match_length S <=? ds_max_lazy_match S) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - zstep. if_cases KC2; zify_cond KC2; rewrite ?unsigned_lit in KC2 by lia.
    +
      eapply KN; [| exact SI'].
      replace (3 <=? ds_lookahead S - ds_match_length S) with false by (symmetry; apply Z.leb_gt; lia). apply andb_false_r.
    + eapply KI; [| exact SI'].
      replace (ds_match_length S <=? ds_max_lazy_match S) with true by (symmetry; apply Z.leb_le; lia).
      replace (3 <=? ds_lookahead S - ds_match_length S) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
End FDIST2.
