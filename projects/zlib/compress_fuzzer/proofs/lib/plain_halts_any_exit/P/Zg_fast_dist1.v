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

Definition dist_regf (ss ms : Z) : Z := bv_swrap 32 (ss - bv_unsigned (sx32 (wz ms))).

Lemma dist_regf_facts : forall ss ms, 0 <= ss <= 65536 -> 0 <= ms < 2^32 ->
  - 2^31 <= dist_regf ss ms < 2^31 /\ dist_regf ss ms mod 2^32 = (ss - ms) mod 2^32.
Proof.
  intros ss ms Hss Hms. unfold dist_regf.
  assert (E : bv_unsigned (sx32 (wz ms)) mod 2^32 = ms mod 2^32).
  { unfold sx32. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in *.
    Z.div_mod_to_equations. lia. }
  remember (bv_unsigned (sx32 (wz ms))) as u eqn:Eu. clear Eu.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in *. change (2 ^ 31) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Section FDIST1.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Definition KT1F (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (w10 : Z) (m' : mem),
    FINV L flush rest0 lo r me (tdist1 X) m' -> Z.land (w10 mod 18446744073709551616) 65535 = tdist_D X ->
    evt psegs Q (MS (fastR L r y1 y5 y6 y7 (wz w10) (wz (tdist_D X)) y12 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31)
                    F (wz 0x19158) fc None m' (seg_rom psegs)).

Lemma fast_tdist1 : forall (Q : machine_state -> Prop) (X : deflate_state),
  trip_inv X -> 3 <= ds_match_length X -> 1 <= ds_lookahead X <= 65536 -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  KT1F Q X ->
  FKD L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X SV ML3 RLA WS LBS HK. unfold FKD. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI). rename m' into m.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_pend Gpend. open_ct Glt.
  pose proof (ln_pend _ LENS) as Lpend. pose proof (ln_ltf _ LENS) as Lltf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR, Z_FAST_DIST. unfold fast_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 7 zs.
  destruct (dist_regf_facts (ds_strstart X) (ds_match_start X) ltac:(lia) Rms) as [Rdv Edv]. unfold dist_regf in Rdv, Edv.
  remember (bv_swrap 32 (ds_strstart X - bv_unsigned (sx32 (wz (ds_match_start X))))) as dv eqn:Edvdef.
  clear Edvdef. apply box in Edv.
  zs.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (wrap16 (wrap32 (ds_strstart X - ds_match_start X))))
    ltac:(apply tally_b0; exact (unbox _ Edv)).
  do 6 zs.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (wrap16 (wrap32 (ds_strstart X - ds_match_start X))))) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 1)
    (wrap8 (Z.shiftr (wrap16 (wrap32 (ds_strstart X - ds_match_start X))) 8)) ltac:(first [apply tally_b1_mod | apply tally_b1]; exact (unbox _ Edv)).
  do 3 zs.
  zs.
  replace (Z.land (ds_match_length X + -3) 255) with (wrap8 (ds_match_length X - 3)) by (unfold wrap8; f_equal; lia).
  assert (Rlc : 0 <= wrap8 (ds_match_length X - 3) < 256) by (apply wrap8_range).
  do 3 zs.
  pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (wrap16 (wrap32 (ds_strstart X - ds_match_start X))))) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 (Z.shiftr (wrap16 (wrap32 (ds_strstart X - ds_match_start X))) 8)))
    65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 2) (wrap8 (wrap8 (ds_match_length X - 3)))
    ltac:(rewrite unsigned_lit by lia; unfold wrap8; change 255 with (Z.ones 8); rewrite !Z.land_ones by lia; change (2^8) with 256; Z.div_mod_to_equations; lia).
  zs.
  assert (MIB : mem_inv psegs _) by eassumption.
  pose proof (rod_length_code _ MIB) as TLC. unfold Z_LENGTH_CODE in TLC.
  ld8ro TLC length_code_a 256 72944 (wrap8 (ds_match_length X - 3)) lcode Elcode ltac:(pose proof (length_code_range (wrap8 (ds_match_length X - 3)) Rlc); lia).
  clear TLC.
  pose proof (length_code_range (wrap8 (ds_match_length X - 3)) Rlc) as Rcode. rewrite <- Elcode in Rcode.
  zs. zs.
  replace (wz (lcode ≪ 2 + (dl_As L + 212))) with (wz (dl_As L + 212 + 4 * lcode)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (u16arr_read psegs _ (dl_As L + 212) (avct (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573) (2 * (lcode + 257))
                (wz (arr_get (ds_dyn_ltree_fc X) (lcode + 257))) (wa (dl_As L + 212 + 4 * lcode + 1028)) Glt
                (avct_nth_fc _ _ 573 (lcode + 257) ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD. zs. zs. zs.
  pose proof (tally_dd_mod dv (ds_strstart X - ds_match_start X) (unbox _ Edv)) as EDD.
  replace ((ds_strstart X - ds_match_start X + -1) mod 2 ^ 16) with (tdist_D X) in EDD by (unfold tdist_D; reflexivity).
  rewrite EDD. apply box in EDD.
  assert (Rdd : 0 <= tdist_D X) by (unfold tdist_D; apply Z.mod_pos_bound; lia).
  remember (tdist_D X) as dd eqn:Edd.
  ct_store_fc Glt (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573 (dl_As L + 212) (lcode + 257) (wrap16 (arr_get (ds_dyn_ltree_fc X) (lcode + 257) + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rlfc; lia).
  name_mem mC.
  tr_groups MUf WMf.
  subst dd lcode. unfold KT1F, fastR in HK.
  eapply HK; [|exact (unbox _ EDD)].
  split; [split|].
  - exact ZS.
  - unfold tdist1. cbv zeta. constructor;
      [do 5 eexists; exact GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mC L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End FDIST1.
