(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow5 RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section LIT.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma slow_tlit : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r me X m ->
  strip_inv X -> 1 <= ds_strstart X -> ds_strstart X <= 65536 -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  (ds_sym_next X + 3 <> ds_sym_end X -> SK L flush rest0 lo r F fc me Q Z_SLOW_LTAIL (slit1 X)) ->
  (ds_sym_next X + 3 = ds_sym_end X -> SK L flush rest0 lo r F fc me Q 0x19c50 (slit1 X)) ->
  evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x19bcc) fc None m (seg_rom psegs)).

Proof.

  intros until m. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) SV SS1 SS2 WS LBS K1 K2.

  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_pend Gpend. open_ct Glt.
  pose proof (ln_pend _ LENS) as Lpend. pose proof (ln_ltf _ LENS) as Lltf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 212, dl_As L + 2504); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 10 zs. rewrite ?Z.mod_small by lia.
  ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + -1) ltac:(apply Rwb; lia).
  pose proof (Rwb (ds_strstart X + -1) ltac:(lia)) as Rc.
  zs.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0) ltac:(reflexivity).
  do 5 zs.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0)) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 0) ltac:(reflexivity).
  do 7 zs.
  remember (arr_get (ds_window X) (ds_strstart X + -1)) as c eqn:Ec.
  assert (Ewc : wrap8 c = c) by (apply wrap8_id; lia).
  pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 0)) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 0))
    65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 2) (wrap8 (wrap8 c)) ltac:(rewrite unsigned_lit by lia; rewrite !Ewc; reflexivity).
  replace (wz (dl_As L + 212 + c ≪ 2)) with (wz (dl_As L + 212 + 4 * c)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (u16arr_read psegs _ (dl_As L + 212) (avct (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573) (2 * wrap8 c)
                (wz (arr_get (ds_dyn_ltree_fc X) (wrap8 c))) (wa (dl_As L + 212 + 4 * c)) Glt
                (avct_nth_fc _ _ 573 (wrap8 c) ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD.

  zs. zs.

  zs.
  ct_store_fc Glt (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573 (dl_As L + 212) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc X) (wrap8 c) + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rlfc; lia).

  name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : SINV L flush rest0 lo r me (slit1 X) mB).
  { subst c. unfold slit1. cbv zeta. replace (ds_strstart X - 1) with (ds_strstart X + -1) by lia.
    split; [split|].
    - exact ZS.
    - constructor; [do 5 eexists; exact GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - eapply (K1 ltac:(lia)). exact SI'.
  - eapply (K2 ltac:(lia)). exact SI'.

Qed.
End LIT.
