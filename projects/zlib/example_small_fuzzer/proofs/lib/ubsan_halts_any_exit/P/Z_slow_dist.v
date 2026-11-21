(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.

Module Z_slow_dist1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6 LmatchModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section DIST1.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Definition KINS (Q : machine_state -> Prop) (T : deflate_state) (mi : Z) (v11 v12 : word) : Prop :=
  forall (y1 y5 y6 y7 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me T m' ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart T + 1)) v11 v12 (wz mi) (wz (ds_prev_length T - 1)) y15 y16 y17 y18 y19 y25 y28 y29 y30 y31)
                    F (wz 0x197d4) fc None m' (seg_rom psegs)).

Definition KT1 (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (w12 : Z) (m' : mem),
    SINV L flush rest0 lo r me (sdist1 X) m' -> Z.land (w12 mod 18446744073709551616) 65535 = sdist_D X ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart X)) (wz (ds_lookahead X)) (wz w12) (wz (sdist_D X)) y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31)
                    F (wz 0x19750) fc None m' (seg_rom psegs)).

Lemma slow_tdist1 : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r me X m ->
  strip_inv X -> 3 <= ds_prev_length X -> 1 <= ds_lookahead X <= 65536 -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  KT1 Q X ->
  evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) y10 y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x196bc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) SV PL3 RLA WS LBS HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_pend Gpend. open_ct Glt.
  pose proof (ln_pend _ LENS) as Lpend. pose proof (ln_ltf _ LENS) as Lltf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 9 zs.
  destruct (dist_reg_facts (ds_strstart X) (ds_prev_match X) ltac:(lia) Rpm) as [Rdv Edv]. unfold dist_reg in Rdv, Edv.
  remember (bv_swrap 32 (bv_unsigned (wz (ds_strstart X)) + Z.lxor (bv_unsigned (sx32 (wz (ds_prev_match X)))) 18446744073709551615)) as dv eqn:Edvdef.
  clear Edvdef. apply box in Edv.
  zs.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (sdist X)) ltac:(unfold sdist; apply tally_b0; exact (unbox _ Edv)).
  do 7 zs.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (sdist X))) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 1)
    (wrap8 (Z.shiftr (sdist X) 8)) ltac:(unfold sdist; first [apply tally_b1_mod | apply tally_b1]; exact (unbox _ Edv)).
  do 3 zs.
  zs.
  replace (Z.land (ds_prev_length X + -3) 255) with (wrap8 (ds_prev_length X - 3)) by (unfold wrap8; f_equal; lia).
  assert (Rlc : 0 <= wrap8 (ds_prev_length X - 3) < 256) by (apply wrap8_range).
  name_mem mB.
  assert (RLB : relro_clean mB) by (apply (slow_relro L inp rest0 lo r me CTX); unfold slow_W; exact MU).
  (* 1.4: _length_code is file-static, addressed pc-relative (auipc + add): no GOT read *)
  zs. clear RLB.
  do 3 zs.
  pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (sdist X))) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 (Z.shiftr (sdist X) 8)))
    65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 2) (wrap8 (wrap8 (ds_prev_length X - 3)))
    ltac:(rewrite unsigned_lit by lia; unfold wrap8; change 255 with (Z.ones 8); rewrite !Z.land_ones by lia; change (2^8) with 256; Z.div_mod_to_equations; lia).
  zs.
  assert (MIB : mem_inv psegs _) by eassumption.
  pose proof (rod_length_code _ MIB) as TLC. unfold Z_LENGTH_CODE in TLC.
  ld8ro TLC length_code_a 256 72880 (wrap8 (ds_prev_length X - 3)) lcode Elcode ltac:(pose proof (length_code_range (wrap8 (ds_prev_length X - 3)) Rlc); lia).
  clear TLC.
  pose proof (length_code_range (wrap8 (ds_prev_length X - 3)) Rlc) as Rcode. rewrite <- Elcode in Rcode.
  zs. zs.
  replace (wz (lcode ≪ 2 + (dl_As L + 212))) with (wz (dl_As L + 212 + 4 * lcode)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (u16arr_read psegs _ (dl_As L + 212) (avct (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573) (2 * (lcode + 257))
                (wz (arr_get (ds_dyn_ltree_fc X) (lcode + 257))) (wa (dl_As L + 212 + 4 * lcode + 1028)) Glt
                (avct_nth_fc _ _ 573 (lcode + 257) ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD. zs. zs. zs.
  pose proof (tally_dd_mod dv (ds_strstart X - 1 - ds_prev_match X) (unbox _ Edv)) as EDD.
  replace ((ds_strstart X - 1 - ds_prev_match X + -1) mod 2 ^ 16) with (sdist_D X) in EDD by (unfold sdist_D; f_equal; lia).
  rewrite EDD. apply box in EDD.
  assert (Rdd : 0 <= sdist_D X) by (unfold sdist_D; apply Z.mod_pos_bound; lia).
  remember (sdist_D X) as dd eqn:Edd.
  ct_store_fc Glt (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573 (dl_As L + 212) (lcode + 257) (wrap16 (arr_get (ds_dyn_ltree_fc X) (lcode + 257) + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rlfc; lia).
  name_mem mC.
  tr_groups MUf WMf.
  subst dd lcode. unfold KT1 in HK.
  eapply HK; [|exact (unbox _ EDD)].
  split; [split|].
  - exact ZS.
  - unfold sdist1. cbv zeta. constructor;
      [do 5 eexists; exact GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mC L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End DIST1.
End Z_slow_dist1.


Module Z_slow_dist2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_drep.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_slow_dist.Z_slow_dist1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6 LmatchModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section DIST2.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma d_code_idx : forall dd, d_code dd = arr_get dist_code_a (if dd <? 256 then dd else 256 + Z.shiftr dd 7).
Proof. intros dd. unfold d_code. destruct (dd <? 256); reflexivity. Qed.

Lemma slow_tdist2 : forall (Q : machine_state -> Prop) (S : deflate_state) (dd w12 : Z)
    (y1 y5 y6 y7 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r me S m ->
  Z.land (w12 mod 18446744073709551616) 65535 = dd -> 0 <= dd < 32768 ->
  0 <= ds_strstart S <= 65536 -> 1 <= ds_lookahead S <= 65536 -> 3 <= ds_prev_length S <= 258 -> ds_prev_length S - 1 <= ds_lookahead S ->
  3 <= ds_strstart S + ds_lookahead S <= 65536 -> 0 <= ds_sym_next S < 2^18 -> 0 <= ds_sym_end S < 2^18 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc S) i < 65536) ->
  Z_slow_dist1.KINS L flush rest0 lo r F fc me Q (dist2_st (sdist2 S (d_code dd))) (ds_strstart S + ds_lookahead S - 3) (wz (ds_sym_next S)) (wz (ds_sym_end S)) ->
  evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart S)) (wz (ds_lookahead S)) (wz w12) (wz dd) y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31)
                  F (wz 0x19750) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) EDD Rdd Rss Rla Rpl PLLA RSL Rsn Rse Rdfc HK.
  apply box in EDD.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_ct Gdt.
  pose proof (ln_dtf _ LENS) as Ldtf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 2504, dl_As L + 2748)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  zs. zstep.
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases KDD; zify_cond KDD; rewrite ?unsigned_lit in KDD by lia.
    -
      zs. zs. rewrite (unbox _ EDD).
      replace (wz dd) with (wz (if dd <? 256 then dd else 256 + Z.shiftr dd 7)) at 1 by (replace (dd <? 256) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      apply evt_done. reflexivity.
    - zs. zs. zs. zs.
      replace (Z.land ((dd ≫ 7 + 256) mod 18446744073709551616) 65535) with (if dd <? 256 then dd else 256 + Z.shiftr dd 7).
      2:{ replace (dd <? 256) with false by (symmetry; apply Z.ltb_ge; lia).
          change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia.
          rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. change (2^64) with 18446744073709551616. change (2^16) with 65536.
          Z.div_mod_to_equations. lia. }
      apply evt_done. reflexivity. }
  intros ms' ->.
  assert (Rdci : 0 <= (if dd <? 256 then dd else 256 + Z.shiftr dd 7) < 512).
  { destruct (Z.ltb_spec dd 256); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. Z.div_mod_to_equations. lia. }
  pose proof (d_code_idx dd) as EDC.
  remember (if dd <? 256 then dd else 256 + Z.shiftr dd 7) as dci eqn:Edci. clear Edci.
  assert (RLA0 : relro_clean mA) by (apply (slow_relro L inp rest0 lo r me CTX); unfold slow_W; exact MU).
  (* 1.4: _dist_code is file-static, addressed pc-relative (auipc + add): no GOT read *)
  zs. clear RLA0.
  do 4 zs.
  pose proof (rod_dist_code _ MI) as TDC. unfold Z_DIST_CODE in TDC.
  ld8ro TDC dist_code_a 512 72368 dci dc Edc ltac:(pose proof (dist_code_range dci Rdci); lia).
  clear TDC. pose proof (dist_code_range dci Rdci) as Rdc30. rewrite <- Edc in Rdc30. rewrite <- EDC in Edc.
  do 5 zs.
  replace (wz (dl_As L + 2504 + dc ≪ 2)) with (wz (dl_As L + 2504 + 4 * dc)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (u16arr_read psegs _ (dl_As L + 2504) (avct (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61) (2 * dc)
                (wz (arr_get (ds_dyn_dtree_fc S) dc)) (wa (dl_As L + 2504 + 4 * dc)) Gdt
                (avct_nth_fc _ _ 61 dc ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD.
  zs. zs. zs. zs.
  ct_store_fc Gdt (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61 (dl_As L + 2504) dc (wrap16 (arr_get (ds_dyn_dtree_fc S) dc + 1))
    ltac:(first [apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rdfc; lia).
  do 6 zs. name_mem mB.
  tr_groups MUf WMf.
  subst dc. unfold Z_slow_dist1.KINS in HK. unfold slowR in HK.
  replace (wz (ds_strstart S + ds_lookahead S + -3)) with (wz (ds_strstart S + ds_lookahead S - 3)) by (f_equal; lia).
  replace (wz (ds_strstart S + 1)) with (wz (ds_strstart (dist2_st (sdist2 S (d_code dd))) + 1)) by reflexivity.
  replace (wz (ds_prev_length S + -3)) with (wz (ds_prev_length (dist2_st (sdist2 S (d_code dd))) - 1)) by (unfold dist2_st, sdist2; dsred; f_equal; lia).
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold dist2_st, sdist2. constructor;
      [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| do 5 eexists; exact GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma slow_ins : forall (n : nat) (Q : machine_state -> Prop) (X : deflate_state) (mi : Z) (v11 v12 : word),
  ILI X -> ds_prev_length X = Z.of_nat n -> (1 <= n)%nat -> Z.of_nat n <= 258 -> ds_strstart X + Z.of_nat n + 1 <= 65536 -> 0 <= mi -> mi + 2 < 65536 ->
  (forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r me (deflate_slow_insert n X mi) m' ->
     evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart (deflate_slow_insert n X mi) + 1)) v11 v12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31)
                     F (wz 0x198ec) fc None m' (seg_rom psegs))) ->
  Z_slow_dist1.KINS L flush rest0 lo r F fc me Q X mi v11 v12.
Proof.
  induction n as [|n IH]; intros Q X mi v11 v12 HI PLn N1 N258 SSn MI0 MI2 KEXIT; [lia|].
  unfold Z_slow_dist1.KINS. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct (ILI_step X mi HI) as (HI' & ESS' & EPL').
  destruct HI as (Rss & Rih & Rhm & Rwm & Rhs & Rwb & Rhb).
  pose proof CTX as CTX0. destruct CTX0 as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  assert (FIN : forall (a1 a5 a6 a7 a15 a16 a17 a18 a19 a25 a28 a29 a30 a31 : word) (mm : mem),
    SINV L flush rest0 lo r me (insl_st X mi) mm ->
    evt psegs Q (MS (slowR L r a1 a5 a6 a7 (wz flush) (wz (ds_strstart X + 1 + 1)) v11 v12 (wz mi) (wz (ds_prev_length X - 1 + -1)) a15 a16 a17 a18 a19 a25 a28 a29 a30 a31)
                    F (wz 0x197d0) fc None mm (seg_rom psegs))).
  { intros until mm. intros SI'. unfold slowR. zstep.
    if_cases KX; zify_cond KX.
    -
      assert (N0 : n = 0%nat) by (rewrite PLn in KX; Z.div_mod_to_equations; lia).
      subst n. rewrite (slow_insert_last X mi PLn) in KEXIT. unfold slowR in KEXIT.
      replace (wz (ds_strstart X + 2)) with (wz (ds_strstart (insl_st X mi) + 1)) by (rewrite ESS'; f_equal; lia).
      eapply KEXIT. exact SI'.
    -
      assert (N1' : (1 <= n)%nat) by (rewrite PLn in KX; Z.div_mod_to_equations; lia).
      destruct n as [|n']; [lia|].
      rewrite (slow_insert_more n' X mi PLn) in KEXIT.
      replace (wz (ds_strstart X + 2)) with (wz (ds_strstart (insl_st X mi) + 1)) by (rewrite ESS'; f_equal; lia).
      replace (wz (ds_prev_length X - 1 + -1)) with (wz (ds_prev_length (insl_st X mi) - 1)) by (rewrite EPL'; f_equal; lia).
      eapply (IH Q (insl_st X mi) mi v11 v12 HI'); [rewrite EPL', PLn; lia| lia| lia| rewrite ESS'; lia| exact MI0| exact MI2| exact KEXIT| exact SI']. }
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUs.
  zs. zstep.
  if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
  -
    do 3 zs. name_mem mB. clear MUf.
    tr_groups MUs WMf.
    eapply FIN.
    unfold insl_st. replace (ds_strstart X + 1 <=? mi) with false by (symmetry; apply Z.leb_gt; lia).
    split; [split|].
    + exact ZS.
    + constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    + split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUs WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
  -
    name_mem mS.
    assert (GwinS : dwin mS L X) by (apply (dwin_munch mA mS L X _ Gwin MUs WMf); cbn [disjoint_from]; slia).
    assert (GprevS : dprev mS L X) by (apply (dprev_munch mA mS L X _ Gprev MUs WMf); cbn [disjoint_from]; slia).
    assert (GheadS : dhead mS L X) by (apply (dhead_munch mA mS L X _ Ghead MUs WMf); cbn [disjoint_from]; slia).
    clear Gwin Gprev Ghead MUs. rename GwinS into Gwin. rename GprevS into Gprev. rename GheadS into Ghead.
    pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mS) as MUg. pose proof (wmono_refl psegs mS) as WMg.
    open_u16 Gprev. open_u16 Ghead.
    pose proof (ln_prev _ LENS) as Lprev. pose proof (ln_head _ LENS) as Lhead.
    do 8 zs. rewrite ?Z.mod_small by lia.
    zs.
    ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + 3) ltac:(apply Rwb; lia).
    zs. zs. zs. zs. zs. zs.
    rewrite (hash_mach X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3))) by lia.
    pose proof (update_hash_range X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3)) ltac:(lia)) as Rhv.
    remember (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3))) as h eqn:Eh.
    zs. zs. rewrite (shl32_shr31 h) by lia. zs.
    pose proof (u16arr_read psegs _ (dl_Ah L) (av16 (ds_head X) 32768) h (wz (arr_get (ds_head X) h)) (wa (dl_Ah L + 2 * h)) Ghead
                  (av16_nth (ds_head X) 32768 h ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. clear RD.
    pose proof (Rhb h ltac:(lia)) as Rhh.
    zs. zs.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite (Z.mul_comm _ 2).
    pose proof (LmatchModel.land_upper_both (ds_strstart X + 1) (ds_w_mask X) ltac:(lia) ltac:(lia)) as Rpi.
    remember (Z.land (ds_strstart X + 1) (ds_w_mask X)) as pi eqn:Epi.
    zs.
    st16 Gprev (ds_prev X) 32768 (dl_Ap L) pi (arr_get (ds_head X) h) ltac:(apply le2_sx16_wz; exact Rhh).
    st16 Ghead (ds_head X) 32768 (dl_Ah L) h (wrap16 (ds_strstart X + 1)) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
    do 4 zs. name_mem mB.
    tr_groups MUf WMf. tr_groups MUg WMg.
    eapply FIN.
    unfold insl_st. replace (ds_strstart X + 1 <=? mi) with true by (symmetry; apply Z.leb_le; lia).
    subst h pi. replace (ds_strstart X + 3) with (ds_strstart X + 1 + 2) in * by lia.
    split; [split|].
    + exact ZS.
    + unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.ins_str. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
    + split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Definition KA (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart X)) y11 y12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x19900) fc None m' (seg_rom psegs)).

Lemma slow_dexit : forall (Q : machine_state -> Prop) (Xf : deflate_state) (sn se : Z)
    (y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r me Xf m -> 0 <= sn < 2^32 -> 0 <= se < 2^32 ->
  (sn <> se -> SK L flush rest0 lo r F fc me Q Z_SLOW_HEAD (exit_st Xf)) ->
  (sn = se -> KA Q (exit_st Xf)) ->
  evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart Xf + 1)) (wz sn) (wz se) y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x198ec) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) Rsn Rse KH0 KA0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 4 zs. name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : SINV L flush rest0 lo r me (exit_st Xf) mB).
  { split; [split|].
    - exact ZS.
    - unfold exit_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - eapply (KH0 KB). exact SI'.
  - unfold KA in KA0. replace (wz (ds_strstart Xf + 1)) with (wz (ds_strstart (exit_st Xf))) by reflexivity.
    eapply (KA0 KB). exact SI'.
Qed.

End DIST2.
End Z_slow_dist2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_slow_dist.Z_slow_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_slow_dist.Z_slow_dist2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6 LmatchModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.LmatchModel.

Module Z_slow_fbA.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk DeflateOverlay SendModel FillWinModel RefFlushBlk13 RefDeflFast1 RefDeflFastM RefDeflFast6 ZCorollaries.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateOverlay OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZCorollaries.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FB.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HTFBLK : tr_flush_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma slow_fbA : forall (Q : machine_state -> Prop) (X : deflate_state)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x28 x29 x30 x31 : word) (m : mem),
  SINV L flush rest0 lo r me X m ->
  flush_ok X 0 -> ds_lit_bufsize X = 16384 -> ds_w_size X = 32768 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  (length (cs_out_rev (ds_strm (flush_block_only X 0))) <= length rest0)%nat ->
  SK L flush rest0 lo r F fc me Q 0x199e0 (flush_block_only X 0) ->
  evt psegs Q (MS (slowR L r x1 x5 x6 x7 (wz flush) (wz (ds_strstart X)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x28 x29 x30 x31) F (wz 0x19900) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & _ & (j0 & FR) & STK & MU & WM & MI) FOK LBS WSX RAO ROOM HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp.
  apply box in SP16.
  assert (OL0 : (length (cs_out_rev (ds_strm X)) <= length rest0)%nat) by (pose proof (fbo_out_mono X 0); lia).
  pose proof (outv_length rest0 (ds_strm X) OL0) as OL. clear OL0.
  apply box in ROOM.
  destruct (fbo_buf_ok X 0 FOK WSX) as (BOK & ELEN & EBP & EBN).
  destruct (flush_ok_fbo X 0 FOK LBS) as (FBS & BI & Rdiff & Rbs & Rss & Rla & Rwb & BI9 & PB10 & RP10 & RPO10 & RPOL & RTO).
  rewrite WSX in Rss, Rla.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  assert (RBS : - 2^63 <= ds_block_start X < 2^63) by lia.
  zs. zs.
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases KB; zify_cond KB.
    -
      assert (NEG : ds_block_start X < 0) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      do 6 zs. rewrite ?Z.mod_small by lia.
      replace (wz 0) with (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end)) at 1 by (rewrite (EBN NEG); reflexivity).
      apply evt_done. reflexivity.
    - assert (POS : 0 <= ds_block_start X) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      do 10 zs. rewrite ?Z.mod_small by lia.
      replace (wz (dl_Aw L + Z.land (ds_block_start X) 4294967295)) with (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end))
        by (rewrite (EBP POS); fold (wrap32 (ds_block_start X)); rewrite wrap32_id by lia; reflexivity).
      apply evt_done. reflexivity. }
  intros ms' ->.
  replace (wz (ds_strstart X - ds_block_start X mod 18446744073709551616)) with (wz (fb_len X))
    by (apply Z_to_bv_eqm; rewrite ELEN; Z.div_mod_to_equations; lia).
  zs.
  assert (RL : relro_clean m) by (apply (slow_relro L inp rest0 lo r me CTX); exact MU).
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  unfold dout in DOUT.
  call (HTFBLK L X (fb_buf X) (fb_len X) 0 lo).
  1:{ exact DR0. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. } 1:{ unfold Z_TRFB_STACK in *. lia. }
  1:{ rewrite ESP. pose proof (unbox _ SP16). Z.div_mod_to_equations. lia. }
  1:{ unfold dlay_below. lia. }
  1:{ exact BI. } 1:{ exact FBS. } 1:{ exact BOK. } 1:{ unfold fb_len. apply wrap64_range. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA. rewrite ESP in PC.
  change (tr_flush_block X (fb_buf X) (fb_len X) 0) with (fbo1 X 0) in POST.
  pose proof (fbo_eq X 0) as EFB.
  destruct (tfb_keep X 0) as (E1 & _ & EO & EAO). pose proof (fbo3_strm X 0) as ES.
  unfold fbo3, fbo2 in EFB, ES, BI9, PB10, RP10, RPO10, RPOL, RTO.
  remember (fbo1 X 0) as X1 eqn:EX1.
  assert (DOUT1 : u8arr psegs mA (dl_NO L) (outv rest0 (ds_strm X1))) by (unfold outv; rewrite EO; exact DOUT).
  assert (OL1 : length (outv rest0 (ds_strm X1)) = length rest0) by (unfold outv; rewrite EO; exact OL).
  assert (RAO1 : 0 <= cs_avail_out (ds_strm X1) < 2^31) by (rewrite EAO; exact RAO).
  clear DOUT OL.
  destruct POST as [ZS ST]. open_zs ZS.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS1 LAY1]. open_A GA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 4 zs. name_mem mB.
  tr_groups MUf WMf.
  remember (set_block_start X1 (ds_strstart X1)) as X2 eqn:EX2.
  assert (ST2 : DST mB L X2).
  { rewrite EX2. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS1 | exact LAY1]. }
  clear MUf WMf GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  zs. zs.
  call (HTFB L X2).
  1:{ exact ST2. } 1:{ eassumption. } 1:{ exact BI9. } 1:{ exact PB10. } 1:{ reflexivity. }
  name_mem mC.
  remember (tr_flush_bits X2) as d1 eqn:Ed1.
  assert (EL : fp_len d1 = if cs_avail_out (ds_strm X1) <? ds_pending d1 then cs_avail_out (ds_strm X1) else ds_pending d1).
  { unfold fp_len. rewrite ES, wrap32_id by lia. reflexivity. }
  remember (fp_len d1) as flen eqn:Eflen. clear Eflen.
  clear FOK LBS WSX RAO BOK ELEN EBP EBN FBS BI Rdiff Rbs Rss Rla Rwb DR0 RBS RL E1 EO EAO ST2 LENS I0 BI9 PB10 EX1 EX2 Ed1.
  destruct POST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSd LAYd]. open_A GA.
  pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] mC) as MUf.
  pose proof (wmono_refl psegs mC) as WMf.
  zs. zs. zstep. (* 1.4: ld pending whole, lwu avail_out *)
  assert (FL : 0 <= flen /\ flen <= cs_avail_out (ds_strm X1) /\ flen <= ds_pending d1) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm X1)) (ds_pending d1)); lia).
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - replace (cs_avail_out (ds_strm X1) <? ds_pending d1) with false in EL by (symmetry; apply Z.ltb_ge; lia).
      replace (wz (ds_pending d1)) with (wz flen) by (f_equal; lia). apply evt_done. reflexivity.
    - assert (EA : flen = cs_avail_out (ds_strm X1)) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm X1)) (ds_pending d1)); lia).
      zstep. apply evt_done. rewrite EA. reflexivity. }
  intros ms' ->. clear EL.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  -
    assert (SI : SINV L flush rest0 lo r me (flush_block_only X 0) mC).
    { replace (flen =? 0) with true in EFB by (symmetry; apply Z.eqb_eq; lia).
      split; [rewrite EFB; split|split; [rewrite EFB|split; [exact ROOM|]]].
      - rewrite ES. do 4 eexists. exact ZS.
      - constructor; [do 5 eexists; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENSd| exact LAYd].
      - rewrite ES; exact DOUT1.
      - split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    eapply HK. exact SI.
  -
    replace (flen =? 0) with false in EFB by (symmetry; apply Z.eqb_neq; lia).
    do 4 zstep. rewrite ?Z.mod_small by lia.
    remember (length (cs_out_rev (ds_strm X1))) as k eqn:Ek.
    assert (KL : (k + Z.to_nat flen <= length rest0)%nat).
    { apply unbox in ROOM. rewrite EFB, fp_tail_out, cs_emit_out_len', ES, <- Ek, arr_slice_length' in ROOM. lia. }
    pose proof (u8arr_sub_bytes _ (dl_Ab L) _ (Z.to_nat (ds_pending_out d1)) (Z.to_nat flen) Gpend ltac:(rewrite av8_length; lia)) as SRC.
    rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
    assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) = Z.to_nat flen)
      by (rewrite length_map; apply arr_slice_length').
    destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat flen) DOUT1 ltac:(rewrite OL1; lia)) as (O1 & O2 & O3). clear DOUT1.
    assert (LO1 : length (firstn k (outv rest0 (ds_strm X1))) = k) by (rewrite length_firstn, OL1; lia).
    assert (LO3 : length (skipn (k + Z.to_nat flen) (outv rest0 (ds_strm X1))) = (length rest0 - (k + Z.to_nat flen))%nat) by (rewrite length_skipn, OL1; lia).
    call (memcpy_Z (dl_NO L + Z.of_nat k) (dl_Ab L + ds_pending_out d1) flen).
    1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat flen) LO1 O1 PC0 O3) as OUT.
    fold (zb8 (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) in OUT.
    rewrite <- (arr_slice_length' (ds_pending_buf d1) (ds_pending_out d1) flen) in OUT. rewrite Ek in OUT.
    rewrite <- outv_emit in OUT by (rewrite <- Ek, arr_slice_length'; exact KL).
    assert (OL' : length (outv rest0 (cs_emit (ds_strm X1) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen))) = length rest0).
    { apply outv_length. rewrite cs_emit_out_len, arr_slice_length', <- Ek. lia. }
    clear O1 O3 PC0 POST SRC LSRC LO1 LO3.
    do 16 zs.
    if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    +
      unfold fp_tail in EFB. cbv zeta in EFB. replace (ds_pending d1 - flen =? 0) with false in EFB by (symmetry; apply Z.eqb_neq; lia).
      tr_groups MUf WMf.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SI : SINV L flush rest0 lo r me (flush_block_only X 0) mm) end.
      { split; [rewrite EFB; split|split; [rewrite EFB|split; [exact ROOM|]]].
        - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
          rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
        - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                       | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
        - rewrite ES; dsred; exact OUT.
        - split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
      eapply HK. exact SI.
    +
      do 2 zs.
      unfold fp_tail in EFB. cbv zeta in EFB. replace (ds_pending d1 - flen =? 0) with true in EFB by (symmetry; apply Z.eqb_eq; lia).
      tr_groups MUf WMf.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SI : SINV L flush rest0 lo r me (flush_block_only X 0) mm) end.
      { split; [rewrite EFB; split|split; [rewrite EFB|split; [exact ROOM|]]].
        - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
          rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
        - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                       | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
        - rewrite ES; dsred; exact OUT.
        - split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
      eapply HK. exact SI.
Qed.
End FB.
End Z_slow_fbA.

Module Z_slow_fbB.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit F_memcpy.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk DeflateOverlay SendModel FillWinModel RefFlushBlk13 RefDeflFast1 RefDeflFastM RefDeflFast6 ZCorollaries.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateOverlay OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZCorollaries.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FBB.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HTFBLK : tr_flush_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma slow_fbB : forall (Q : machine_state -> Prop) (X : deflate_state)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x28 x29 x30 x31 : word) (m : mem),
  SINV L flush rest0 lo r me X m ->
  flush_ok X 0 -> ds_lit_bufsize X = 16384 -> ds_w_size X = 32768 -> 0 <= cs_avail_out (ds_strm X) < 2^31 ->
  (length (cs_out_rev (ds_strm (flush_block_only X 0))) <= length rest0)%nat ->
  SK L flush rest0 lo r F fc me Q Z_SLOW_LTAIL (flush_block_only X 0) ->
  evt psegs Q (MS (slowR L r x1 x5 x6 x7 (wz flush) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x28 x29 x30 x31) F (wz 0x198d0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & _ & (j0 & FR) & STK & MU & WM & MI) FOK LBS WSX RAO ROOM HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp.
  apply box in SP16.
  assert (OL0 : (length (cs_out_rev (ds_strm X)) <= length rest0)%nat) by (pose proof (fbo_out_mono X 0); lia).
  pose proof (outv_length rest0 (ds_strm X) OL0) as OL. clear OL0.
  apply box in ROOM.
  destruct (fbo_buf_ok X 0 FOK WSX) as (BOK & ELEN & EBP & EBN).
  destruct (flush_ok_fbo X 0 FOK LBS) as (FBS & BI & Rdiff & Rbs & Rss & Rla & Rwb & BI9 & PB10 & RP10 & RPO10 & RPOL & RTO).
  rewrite WSX in Rss, Rla.
  pose proof DR as DR0. destruct DR as [ZS ST]. open_DST ST. open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  assert (RBS : - 2^63 <= ds_block_start X < 2^63) by lia.
  unfold Z_SLOW_LTAIL in HK.
  zs. zs.
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases KB; zify_cond KB.
    -
      assert (NEG : ds_block_start X < 0) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      do 5 zs. rewrite ?Z.mod_small by lia.
      replace (wz 0) with (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end)) at 1 by (rewrite (EBN NEG); reflexivity).
      apply evt_done. reflexivity.
    - assert (POS : 0 <= ds_block_start X) by (change (2^63) with 9223372036854775808 in RBS; Z.div_mod_to_equations; lia).
      do 9 zs. rewrite ?Z.mod_small by lia.
      replace (wz (dl_Aw L + Z.land (ds_block_start X) 4294967295)) with (wz (match fb_buf X with Some off => dl_Aw L + off | None => 0 end))
        by (rewrite (EBP POS); fold (wrap32 (ds_block_start X)); rewrite wrap32_id by lia; reflexivity).
      apply evt_done. reflexivity. }
  intros ms' ->.
  replace (wz (ds_strstart X - ds_block_start X mod 18446744073709551616)) with (wz (fb_len X))
    by (apply Z_to_bv_eqm; rewrite ELEN; Z.div_mod_to_equations; lia).
  zs.
  assert (RL : relro_clean m) by (apply (slow_relro L inp rest0 lo r me CTX); exact MU).
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
  clear GA ZS GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  unfold dout in DOUT.
  call (HTFBLK L X (fb_buf X) (fb_len X) 0 lo).
  1:{ exact DR0. } 1:{ exact MI. } 1:{ exact RL. } 1:{ rewrite ESP. exact STK. } 1:{ unfold Z_TRFB_STACK in *. lia. }
  1:{ rewrite ESP. pose proof (unbox _ SP16). Z.div_mod_to_equations. lia. }
  1:{ unfold dlay_below. lia. }
  1:{ exact BI. } 1:{ exact FBS. } 1:{ exact BOK. } 1:{ unfold fb_len. apply wrap64_range. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mA. rewrite ESP in PC.
  change (tr_flush_block X (fb_buf X) (fb_len X) 0) with (fbo1 X 0) in POST.
  pose proof (fbo_eq X 0) as EFB.
  destruct (tfb_keep X 0) as (E1 & _ & EO & EAO). pose proof (fbo3_strm X 0) as ES.
  unfold fbo3, fbo2 in EFB, ES, BI9, PB10, RP10, RPO10, RPOL, RTO.
  remember (fbo1 X 0) as X1 eqn:EX1.
  assert (DOUT1 : u8arr psegs mA (dl_NO L) (outv rest0 (ds_strm X1))) by (unfold outv; rewrite EO; exact DOUT).
  assert (OL1 : length (outv rest0 (ds_strm X1)) = length rest0) by (unfold outv; rewrite EO; exact OL).
  assert (RAO1 : 0 <= cs_avail_out (ds_strm X1) < 2^31) by (rewrite EAO; exact RAO).
  clear DOUT OL.
  destruct POST as [ZS ST]. open_zs ZS.
  destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS1 LAY1]. open_A GA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 4 zs. name_mem mB.
  tr_groups MUf WMf.
  remember (set_block_start X1 (ds_strstart X1)) as X2 eqn:EX2.
  assert (ST2 : DST mB L X2).
  { rewrite EX2. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS1 | exact LAY1]. }
  clear MUf WMf GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend.
  zs. zs.
  call (HTFB L X2).
  1:{ exact ST2. } 1:{ eassumption. } 1:{ exact BI9. } 1:{ exact PB10. } 1:{ reflexivity. }
  name_mem mC.
  remember (tr_flush_bits X2) as d1 eqn:Ed1.
  assert (EL : fp_len d1 = if cs_avail_out (ds_strm X1) <? ds_pending d1 then cs_avail_out (ds_strm X1) else ds_pending d1).
  { unfold fp_len. rewrite ES, wrap32_id by lia. reflexivity. }
  remember (fp_len d1) as flen eqn:Eflen. clear Eflen.
  clear FOK LBS WSX RAO BOK ELEN EBP EBN FBS BI Rdiff Rbs Rss Rla Rwb DR0 RBS RL E1 EO EAO ST2 LENS I0 BI9 PB10 EX1 EX2 Ed1.
  destruct POST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENSd LAYd]. open_A GA.
  pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] mC) as MUf.
  pose proof (wmono_refl psegs mC) as WMf.
  zs. zs. zstep. (* 1.4: ld pending whole, lwu avail_out *)
  assert (FL : 0 <= flen /\ flen <= cs_avail_out (ds_strm X1) /\ flen <= ds_pending d1) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm X1)) (ds_pending d1)); lia).
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - replace (cs_avail_out (ds_strm X1) <? ds_pending d1) with false in EL by (symmetry; apply Z.ltb_ge; lia).
      replace (wz (ds_pending d1)) with (wz flen) by (f_equal; lia). apply evt_done. reflexivity.
    - assert (EA : flen = cs_avail_out (ds_strm X1)) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm X1)) (ds_pending d1)); lia).
      zstep. apply evt_done. rewrite EA. reflexivity. }
  intros ms' ->. clear EL.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  -
    assert (SI : SINV L flush rest0 lo r me (flush_block_only X 0) mC).
    { replace (flen =? 0) with true in EFB by (symmetry; apply Z.eqb_eq; lia).
      split; [rewrite EFB; split|split; [rewrite EFB|split; [exact ROOM|]]].
      - rewrite ES. do 4 eexists. exact ZS.
      - constructor; [do 5 eexists; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                     | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENSd| exact LAYd].
      - rewrite ES; exact DOUT1.
      - split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
    eapply HK. exact SI.
  -
    replace (flen =? 0) with false in EFB by (symmetry; apply Z.eqb_neq; lia).
    do 4 zstep. rewrite ?Z.mod_small by lia.
    remember (length (cs_out_rev (ds_strm X1))) as k eqn:Ek.
    assert (KL : (k + Z.to_nat flen <= length rest0)%nat).
    { apply unbox in ROOM. rewrite EFB, fp_tail_out, cs_emit_out_len', ES, <- Ek, arr_slice_length' in ROOM. lia. }
    pose proof (u8arr_sub_bytes _ (dl_Ab L) _ (Z.to_nat (ds_pending_out d1)) (Z.to_nat flen) Gpend ltac:(rewrite av8_length; lia)) as SRC.
    rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
    assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) = Z.to_nat flen)
      by (rewrite length_map; apply arr_slice_length').
    destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat flen) DOUT1 ltac:(rewrite OL1; lia)) as (O1 & O2 & O3). clear DOUT1.
    assert (LO1 : length (firstn k (outv rest0 (ds_strm X1))) = k) by (rewrite length_firstn, OL1; lia).
    assert (LO3 : length (skipn (k + Z.to_nat flen) (outv rest0 (ds_strm X1))) = (length rest0 - (k + Z.to_nat flen))%nat) by (rewrite length_skipn, OL1; lia).
    call (memcpy_Z (dl_NO L + Z.of_nat k) (dl_Ab L + ds_pending_out d1) flen).
    1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat flen) LO1 O1 PC0 O3) as OUT.
    fold (zb8 (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen)) in OUT.
    rewrite <- (arr_slice_length' (ds_pending_buf d1) (ds_pending_out d1) flen) in OUT. rewrite Ek in OUT.
    rewrite <- outv_emit in OUT by (rewrite <- Ek, arr_slice_length'; exact KL).
    assert (OL' : length (outv rest0 (cs_emit (ds_strm X1) (arr_slice (ds_pending_buf d1) (ds_pending_out d1) flen))) = length rest0).
    { apply outv_length. rewrite cs_emit_out_len, arr_slice_length', <- Ek. lia. }
    clear O1 O3 PC0 POST SRC LSRC LO1 LO3.
    do 16 zs.
    if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    +
      unfold fp_tail in EFB. cbv zeta in EFB. replace (ds_pending d1 - flen =? 0) with false in EFB by (symmetry; apply Z.eqb_neq; lia).
      tr_groups MUf WMf.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SI : SINV L flush rest0 lo r me (flush_block_only X 0) mm) end.
      { split; [rewrite EFB; split|split; [rewrite EFB|split; [exact ROOM|]]].
        - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
          rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
        - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                       | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
        - rewrite ES; dsred; exact OUT.
        - split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
      eapply HK. exact SI.
    +
      do 3 zs.
      unfold fp_tail in EFB. cbv zeta in EFB. replace (ds_pending d1 - flen =? 0) with true in EFB by (symmetry; apply Z.eqb_eq; lia).
      tr_groups MUf WMf.
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SI : SINV L flush rest0 lo r me (flush_block_only X 0) mm) end.
      { split; [rewrite EFB; split|split; [rewrite EFB|split; [exact ROOM|]]].
        - rewrite ES. eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; unfold cs_emit; dsred;
          rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek; close_cells ZS.
        - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                       | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENSd | exact LAYd].
        - rewrite ES; dsred; exact OUT.
        - split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
      eapply HK. exact SI.
Qed.
End FBB.
End Z_slow_fbB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section DIST.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma slow_dist : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r me X m ->
  strip_inv X -> dist_cond X = true -> sdist_ok 32768 X -> 1 <= ds_lookahead X <= 65536 -> ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  (snd (st_sdist X) = false -> SK L flush rest0 lo r F fc me Q Z_SLOW_HEAD (fst (st_sdist X))) ->
  (snd (st_sdist X) = true -> KA L flush rest0 lo r F fc me Q (fst (st_sdist X))) ->
  evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) y10 y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x196bc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros SI SV DC (PLLA & SL3 & DD & _ & _) RLA WS HS LBS KH0 KA0.
  unfold dist_cond in DC. apply andb_prop in DC. destruct DC as [DC1 _]. apply Z.leb_le in DC1.
  pose proof SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *. rewrite HS in *. rewrite LBS in *.
  destruct (sdist_eq X DC1 PLLA ltac:(lia) SL3 ltac:(lia)) as [EF ES]. rewrite EF, ES in KH0, KA0. clear EF ES.
  eapply (slow_tdist1 L flush inp rest0 lo r F fc me CTX Q X); [exact SI| exact SV| exact DC1| exact RLA| exact WS| exact LBS|].
  unfold KT1. intros until m'. intros SI1 EDD.
  eapply (slow_tdist2 L flush inp rest0 lo r F fc me CTX Q (sdist1 X) (sdist_D X) w12); [exact SI1| exact EDD| | | | | | | | | | ].
  1:{ unfold sdist_D in *. pose proof (Z.mod_pos_bound (ds_strstart X - ds_prev_match X + -2) (2^16) ltac:(lia)). lia. }
  1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. }
  1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. } 1:{ unfold sdist1. dsred. lia. }
  1:{ intros i Hi. unfold sdist1. dsred. apply Rdfc. exact Hi. }
  remember (dist2_st (sdist2 (sdist1 X) (d_code (sdist_D X)))) as T eqn:ET.
  assert (TSS : ds_strstart T = ds_strstart X) by (rewrite ET; unfold dist2_st, sdist2, sdist1; dsred; reflexivity).
  assert (TPL : ds_prev_length T = ds_prev_length X - 2) by (rewrite ET; unfold dist2_st, sdist2, sdist1; dsred; reflexivity).
  assert (TI : ILI T).
  { rewrite ET. unfold ILI, dist2_st, sdist2, sdist1. dsred.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros j Hj; apply Rwb; lia | intros j Hj; apply Rhb; lia]. }
  replace (ds_strstart (sdist1 X) + ds_lookahead (sdist1 X) - 3) with (ds_strstart X + ds_lookahead X - 3) by (unfold sdist1; dsred; reflexivity).
  eapply (slow_ins L flush inp rest0 lo r F fc me CTX (Z.to_nat (ds_prev_length X - 2)) Q T (ds_strstart X + ds_lookahead X - 3)); [exact TI| rewrite TPL; lia| lia| lia| rewrite TSS; lia| lia| lia|].
  intros until m'0. intros SIF.
  eapply (slow_dexit L flush inp rest0 lo r F fc me CTX Q _ (ds_sym_next (sdist1 X)) (ds_sym_end (sdist1 X))); [exact SIF| unfold sdist1; dsred; lia| unfold sdist1; dsred; lia| |].
  - intros NE. apply KH0. apply Z.eqb_neq. unfold sdist1 in NE. dsred in NE. exact NE.
  - intros EQ. apply KA0. apply Z.eqb_eq. unfold sdist1 in EQ. dsred in EQ. exact EQ.
Qed.
End DIST.
