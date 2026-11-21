(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_tr_rod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6 LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section DIST1.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Definition KINS (Q : machine_state -> Prop) (T : deflate_state) (mi : Z) (v11 v12 : word) : Prop :=
  forall (y1 y5 y6 y7 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me T m' ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart T + 1)) v11 v12 (wz mi) (wz (ds_prev_length T - 1)) y15 y16 y17 y18 y19 y25 y28 y29 y30 y31)
                    F (wz 0x19b54) fc None m' (seg_rom psegs)).

Definition KT1 (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (w12 : Z) (m' : mem),
    SINV L flush rest0 lo r me (sdist1 X) m' -> Z.land (w12 mod 18446744073709551616) 65535 = sdist_D X ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart X)) (wz (ds_lookahead X)) (wz w12) (wz (sdist_D X)) y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31)
                    F (wz 0x19ad0) fc None m' (seg_rom psegs)).

Lemma slow_tdist1 : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y10 y11 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r me X m ->
  strip_inv X -> 3 <= ds_prev_length X -> 1 <= ds_lookahead X <= 65536 -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  KT1 Q X ->
  evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) y10 y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x19a3c) fc None m (seg_rom psegs)).
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
  ld8ro TLC length_code_a 256 72976 (wrap8 (ds_prev_length X - 3)) lcode Elcode ltac:(pose proof (length_code_range (wrap8 (ds_prev_length X - 3)) Rlc); lia).
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
