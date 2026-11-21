(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.

Module Z_slow_dist1.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma dist_reg64_facts : forall ss pm, 0 <= ss <= 65536 -> 0 <= pm < 2^32 ->
  0 <= ss + Z.lxor (bv_unsigned (sx32 (wz pm))) 18446744073709551615 < 2^65
  /\ (ss + Z.lxor (bv_unsigned (sx32 (wz pm))) 18446744073709551615) mod 2^32 = (ss - 1 - pm) mod 2^32.
Proof.
  intros ss pm Hss Hpm.
  assert (Rx : 0 <= bv_unsigned (sx32 (wz pm)) < 2^64) by (pose proof (bv_unsigned_in_range 64 (sx32 (wz pm))) as R; unfold bv_modulus in R; cbn in R; lia).
  rewrite (zb_lxor_ones _ Rx).
  assert (E : bv_unsigned (sx32 (wz pm)) mod 2^32 = pm mod 2^32).
  { unfold sx32. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (4294967296 / 2) with 2147483648. change (2 ^ 32) with 4294967296 in *.
    Z.div_mod_to_equations. lia. }
  remember (bv_unsigned (sx32 (wz pm))) as u eqn:Eu. clear Eu.
  change (2 ^ 32) with 4294967296 in *. change (2^65) with 36893488147419103232. change (2^64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma tally_b1w : forall dv e, 0 <= dv -> dv mod 2^32 = e mod 2^32 ->
  bv_unsigned (wz (bv_swrap 32 (Z.shiftr (bv_wrap 32 (dv mod 18446744073709551616)) 8))) mod 2^8 = wrap8 (Z.shiftr (wrap16 (wrap32 e)) 8) mod 2^8.
Proof.
  intros dv e Hdv E.
  assert (EW : bv_wrap 32 (dv mod 18446744073709551616) = e mod 2^32).
  { unfold bv_wrap, bv_modulus. cbn [Z.of_N]. change (2^32) with 4294967296 in *. rewrite <- E.
    Z.div_mod_to_equations. nia. }
  rewrite EW. pose proof (Z.mod_pos_bound e (2^32) ltac:(lia)) as R.
  assert (RS : 0 <= Z.shiftr (e mod 2^32) 8 < 2^24) by (rewrite Z.shiftr_div_pow2 by lia; change (2^32) with 4294967296 in *; change (2^8) with 256; change (2^24) with 16777216; Z.div_mod_to_equations; lia).
  rewrite bv_swrap32_id by lia. rewrite unsigned_lit by lia.
  unfold wrap8, wrap16, wrap32. change 255 with (Z.ones 8). change 65535 with (Z.ones 16). change 4294967295 with (Z.ones 32). rewrite !Z.land_ones by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 32) with 4294967296 in *. change (2^16) with 65536. change (2^8) with 256.
  Z.div_mod_to_equations. lia.
Qed.

Lemma tally_dd64 : forall dv e, 0 <= dv -> dv mod 2^32 = e mod 2^32 ->
  ((dv + -1) mod 18446744073709551616) mod 65536 = (e + -1) mod 2^16.
Proof.
  intros dv e Hdv E. change (2 ^ 32) with 4294967296 in *. change (2^16) with 65536.
  Z.div_mod_to_equations. nia.
Qed.

Lemma shl48_eqm : forall x d, 0 <= x -> x mod 65536 = d -> wz (Z.shiftl x 48) = wz (d * 281474976710656).
Proof.
  intros x d Hx E. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. change (2^48) with 281474976710656. change (2^64) with 18446744073709551616.
  rewrite <- E. Z.div_mod_to_equations. nia.
Qed.

Section DIST1.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Definition KT1 (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me (sdist1 X) m' ->
    (* 1.4 UBSan: the d_code prelude (auipc a2; sll a4,a3,48; srl a3,a4,48) now runs before tdist2, so KT1 sits at the add
       that completes &_dist_code (0x19f28): a2 = the auipc page 0x11f7c, a3 = dd, a4 = dd << 48. *)
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart X)) (wz (ds_lookahead X)) (wz 73596) (wz (sdist_D X)) (wz (sdist_D X * 281474976710656)) y15 y16 y17 y28 y29 y30 y31)
                    F (wz 0x19f88) fc None m' (seg_rom usegs)).

Lemma slow_tdist1 : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y11 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  strip_inv X -> 3 <= ds_prev_length X -> 1 <= ds_lookahead X <= 65536 -> ds_w_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  KT1 Q X ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_match_length X)) y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x19e94) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) SV PL3 RLA WS LBS HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_pend Gpend. open_ct Glt.
  pose proof (ln_pend _ LENS) as Lpend. pose proof (ln_ltf _ LENS) as Lltf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_b _ LAY) as BKb. unfold blk_ok in BKb. pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L + 212, dl_As L + 2504); (dl_As L + 5881, dl_As L + 5968); (dl_Ab L, dl_Ab L + 65536)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. zs. zs. zs. zs. rewrite ?(sx32_wz (ds_strstart X)) by lia. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  zstep. zstep.
  destruct (dist_reg64_facts (ds_strstart X) (ds_prev_match X) ltac:(lia) Rpm) as [Rdv Edv].
  remember (ds_strstart X + Z.lxor (bv_unsigned (sx32 (wz (ds_prev_match X)))) 18446744073709551615) as dv eqn:Edvdef.
  clear Edvdef. apply box in Edv.
  pb_store Gpend (ds_pending_buf X) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (sdist X)) ltac:(unfold sdist; apply tally_b0; exact (unbox _ Edv)).
  zs. zs. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  zstep.
  pb_store Gpend (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (sdist X))) 65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 1)
    (wrap8 (Z.shiftr (sdist X) 8)) ltac:(unfold sdist; apply tally_b1w; [lia| exact (unbox _ Edv)]).
  zs. zs. zstep. zstep. zs. gF. zstep. zstep. zstep. gX. gF.
  name_mem mB.
  (* 1.4 UBSan: add a6,a2,-3; auipc a5; zext.b a2,a6; add a5,a5,-556 = &_length_code, pc-relative (no GOT read) *)
  zstep. zstep. zstep. zstep.
  replace (Z.land (ds_prev_length X + -3) 255) with (wrap8 (ds_prev_length X - 3)) by (unfold wrap8; f_equal; lia).
  assert (Rlc : 0 <= wrap8 (ds_prev_length X - 3) < 256) by (apply wrap8_range).
  zstep. try rewrite (zb_lxor_ones 72880) by lia.
  pb_store Gpend (arr_set (arr_set (ds_pending_buf X) (ds_lit_bufsize X + ds_sym_next X) (wrap8 (sdist X))) (ds_lit_bufsize X + ds_sym_next X + 1) (wrap8 (Z.shiftr (sdist X) 8)))
    65536 (dl_Ab L) (ds_lit_bufsize X + ds_sym_next X + 2) (wrap8 (wrap8 (ds_prev_length X - 3)))
    ltac:(rewrite unsigned_lit by lia; unfold wrap8; change 255 with (Z.ones 8); rewrite !Z.land_ones by lia; change (2^8) with 256; Z.div_mod_to_equations; lia).
  gF. zstep.
  assert (MIB : mem_inv usegs _) by eassumption.
  pose proof (rod_length_code _ MIB) as TLC. unfold Z_LENGTH_CODE in TLC.
  ld8ro TLC length_code_a 256 72880 (wrap8 (ds_prev_length X - 3)) lcode Elcode ltac:(pose proof (length_code_range (wrap8 (ds_prev_length X - 3)) Rlc); lia).
  clear TLC.
  pose proof (length_code_range (wrap8 (ds_prev_length X - 3)) Rlc) as Rcode. rewrite <- Elcode in Rcode.
  zstep. zstep. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. gF. zstep.
  pose proof (u16arr_read usegs _ (dl_As L + 212) (avct (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573) (2 * (lcode + 257))
                (wz (arr_get (ds_dyn_ltree_fc X) (lcode + 257))) (wa (dl_As L + 212 + (lcode + 257) * 4)) Glt
                (avct_nth_fc _ _ 573 (lcode + 257) ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD. zstep. zstep.
  ct_store_fc Glt (ds_dyn_ltree_fc X) (ds_dyn_ltree_dl X) 573 (dl_As L + 212) (lcode + 257) (wrap16 (arr_get (ds_dyn_ltree_fc X) (lcode + 257) + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rlfc; lia).
  (* 1.4 UBSan: the d_code prelude follows the ltree store: auipc a2; sll a4,a3,0x30; srl a3,a4,0x30 *)
  zstep. zstep. zstep.
  rewrite (tally_dd64 dv (ds_strstart X - 1 - ds_prev_match X) ltac:(lia) (unbox _ Edv)).
  replace ((ds_strstart X - 1 - ds_prev_match X + -1) mod 2 ^ 16) with (sdist_D X) by (unfold sdist_D; f_equal; lia).
  rewrite (shl48_eqm ((dv + -1) mod 18446744073709551616) (sdist_D X) ltac:(Z.div_mod_to_equations; lia)
             ltac:(rewrite (tally_dd64 dv (ds_strstart X - 1 - ds_prev_match X) ltac:(lia) (unbox _ Edv)); unfold sdist_D; f_equal; lia)).
  name_mem mC.
  tr_groups MUf WMf.
  subst lcode. unfold KT1, slowR in HK.
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold sdist1. cbv zeta. constructor;
      [do 5 eexists; exact GA | exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mC L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.
End DIST1.
End Z_slow_dist1.


Module Z_slow_dist2.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_drep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_ukit.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_ukit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_dist.Z_slow_dist1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel LmatchModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.LmatchModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section DIST2.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Definition KINS (Q : machine_state -> Prop) (T : deflate_state) (mi : Z) (v11 v12 : word) : Prop :=
  forall (y1 y5 y6 y7 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me T m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart T + 1)) v11 v12 (wz mi) (wz (ds_prev_length T - 1)) y15 y16 y17 y28 y29 y30 y31)
                    F (wz 0x1a01c) fc None m' (seg_rom usegs)).

Lemma shr55_7 : forall dd, 0 <= dd -> Z.shiftr (dd * 281474976710656) 55 = Z.shiftr dd 7.
Proof.
  intros dd Hd. rewrite !Z.shiftr_div_pow2 by lia. change (2^55) with (281474976710656 * 128). change (2^7) with 128.
  rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma d_code_idx : forall dd, d_code dd = arr_get dist_code_a (if dd <? 256 then dd else 256 + Z.shiftr dd 7).
Proof. intros dd. unfold d_code. destruct (dd <? 256); reflexivity. Qed.

Lemma slow_tdist2 : forall (Q : machine_state -> Prop) (S : deflate_state) (dd : Z)
    (y1 y5 y6 y7 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me S m ->
  0 <= dd < 32768 ->
  0 <= ds_strstart S <= 65536 -> 1 <= ds_lookahead S <= 65536 -> 3 <= ds_prev_length S <= 258 -> ds_prev_length S - 1 <= ds_lookahead S ->
  3 <= ds_strstart S + ds_lookahead S <= 65536 -> 0 <= ds_sym_next S < 2^18 -> 0 <= ds_sym_end S < 2^18 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc S) i < 65536) ->
  KINS Q (dist2_st (sdist2 S (d_code dd))) (ds_strstart S + ds_lookahead S - 3) (wz (ds_sym_next S)) (wz (ds_sym_end S)) ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart S)) (wz (ds_lookahead S)) (wz 73596) (wz dd) (wz (dd * 281474976710656)) y15 y16 y17 y28 y29 y30 y31)
                  F (wz 0x19f88) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) Rdd Rss Rla Rpl PLLA RSL Rsn Rse Rdfc HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_ct Gdt.
  pose proof (ln_dtf _ LENS) as Ldtf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 2504, dl_As L + 2748)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.

  assert (Rdci : 0 <= (if dd <? 256 then dd else 256 + Z.shiftr dd 7) < 512).
  { destruct (Z.ltb_spec dd 256); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. Z.div_mod_to_equations. lia. }
  (* 1.4 UBSan: add a2,a2,-1132 (= &_dist_code, pc-relative); li a5,255; bgeu a5,a3 (dd < 256 skips the >> 7 index) *)
  zstep. zstep. zstep.
  eapply (evt_cut usegs (fun ms' => exists v14, ms' = MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart S)) (wz (ds_lookahead S)) (wz 72368) (wz (if dd <? 256 then dd else 256 + Z.shiftr dd 7)) v14 (wz 255) y16 y17 y28 y29 y30 y31)
                                                              F (wz 0x19f9c) fc None mA (seg_rom usegs))).
  { if_cases KDD; zify_cond KDD; rewrite ?unsigned_lit in KDD by lia.
    - (* bgeu taken: dd <= 255, the index is dd *)
      apply evt_done. eexists. unfold slowR.
      replace (dd <? 256) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - (* dd >= 256: srl a4,a4,0x37; add a3,a4,256 *)
      zstep. rewrite (shr55_7 dd) by lia. zstep.
      apply evt_done. eexists. unfold slowR.
      replace (dd <? 256) with false by (symmetry; apply Z.ltb_ge; lia). replace (dd ≫ 7 + 256) with (256 + dd ≫ 7) by lia. reflexivity. }
  intros ms' (v14 & ->). unfold slowR.
  pose proof (d_code_idx dd) as EDC.
  remember (if dd <? 256 then dd else 256 + Z.shiftr dd 7) as dci eqn:Edci. clear Edci.
  (* not a4,a2; bltu a4,a3 (trap); add a2,a2,a3 *)
  zstep. try rewrite (zb_lxor_ones 72368) by lia. gF. zstep.
  pose proof (rod_dist_code _ MI) as TDC. unfold Z_DIST_CODE in TDC.
  ld8ro TDC dist_code_a 512 72368 dci dc Edc ltac:(pose proof (dist_code_range dci Rdci); lia).
  clear TDC. pose proof (dist_code_range dci Rdci) as Rdc30. rewrite <- Edc in Rdc30. rewrite <- EDC in Edc.
  zstep. gF. zstep. rewrite ?Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. gF. zstep.
  pose proof (u16arr_read usegs _ (dl_As L + 2504) (avct (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61) (2 * dc)
                (wz (arr_get (ds_dyn_dtree_fc S) dc)) (wa (dl_As L + 2504 + dc * 4)) Gdt
                (avct_nth_fc _ _ 61 dc ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD.
  zs. zs. zs. zstep.
  ct_store_fc Gdt (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61 (dl_As L + 2504) dc (wrap16 (arr_get (ds_dyn_dtree_fc S) dc + 1))
    ltac:(first [apply le2_swrap16_inc_mod | apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rdfc; lia).
  zstep. zs. zstep. zstep. zs. zs. zs. zs. zs. zstep. zs. name_mem mB.
  zstep.
  tr_groups MUf WMf.
  subst dc. unfold KINS in HK. unfold slowR in HK.
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
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma slow_ins : forall (n : nat) (Q : machine_state -> Prop) (X : deflate_state) (mi : Z) (v11 v12 : word),
  ILI X -> ds_prev_length X = Z.of_nat n -> (1 <= n)%nat -> Z.of_nat n <= 258 -> ds_strstart X + Z.of_nat n + 1 <= 65536 -> 0 <= mi -> mi + 2 < 65536 ->
  (forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r fj me (deflate_slow_insert n X mi) m' ->
     evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart (deflate_slow_insert n X mi) + 1)) v11 v12 y13 y14 y15 y16 y17 y28 y29 y30 y31)
                     F (wz 0x1a21c) fc None m' (seg_rom usegs))) ->
  KINS Q X mi v11 v12.
Proof.
  induction n as [|n IH]; intros Q X mi v11 v12 HI PLn N1 N258 SSn MI0 MI2 KEXIT; [lia|].
  unfold KINS. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct (ILI_step X mi HI) as (HI' & ESS' & EPL').
  destruct HI as (Rss & Rih & Rhm & Rwm & Rhs & Rwb & Rhb).
  pose proof CTX as CTX0. destruct CTX0 as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  pose proof HFL as HFL'. unfold Z_NO_FLUSH, Z_FINISH in HFL'.
  assert (FIN : forall (Y : deflate_state) (a1 a5 a6 a7 a15 a16 a17 a28 a29 a30 a31 : word) (mm : mem) (k1 k2 k3 k4 k5 : list byte),
    dzs mm L (ds_strm X) ->
    rw_cells usegs mm (dl_As L) (dsA_cells L Y k1 k2 k3 k4 k5) ->
    (forall v k1' k2' k3' k4' k5' mm', munch [(dl_As L, dl_As L + 212)] mm mm' -> wmono usegs mm mm' ->
       rw_cells usegs mm' (dl_As L) (dsA_cells L (set_prev_length Y v) k1' k2' k3' k4' k5') ->
       DST mm' L (set_prev_length (if ds_strstart X + 1 <=? mi then ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1)
                                   else set_strstart X (ds_strstart X + 1)) v)) ->
    dout mm L rest0 (ds_strm X) -> rw_cells usegs mm (bv_unsigned (r_sp r) + -128) (slow_frame fj r) -> stk usegs mm lo (bv_unsigned (r_sp r) + -128) ->
    munch (slow_W L rest0 lo r) me mm -> wmono usegs me mm -> mem_inv usegs mm ->
    evt usegs Q (MS (slowR L flush r a1 a5 a6 a7 (wz (ds_strstart X + 1)) v11 v12 (wz mi) (wz (ds_prev_length X - 1)) a15 a16 a17 a28 a29 a30 a31)
                    F (wz 0x1a00c) fc None mm (seg_rom usegs))).
  { intros until k5. intros ZS GA REST DOUT' FR' STK' MU' WM' MI'. unfold slowR. unfold dsA_cells in GA. unfold slow_frame in FR'. unfold slow_W in MU'.
    lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
    pose proof (munch_refl [(dl_As L, dl_As L + 212)] mm) as MUs. pose proof (wmono_refl usegs mm) as WMs.
    zs. name_mem mB. zs. zs.
    tr_groups MUs WMs.
    assert (ESTRM : ds_strm (insl_st X mi) = ds_strm X) by (unfold insl_st, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.ins_str; destruct (ds_strstart X + 1 <=? mi); reflexivity).
    assert (SI' : SINV L flush rest0 lo r fj me (insl_st X mi) mB).
    { split; [split|].
      - rewrite ESTRM. exact ZS.
      - unfold insl_st. eapply (REST _ _ _ _ _ _ mB MUs WMs). unfold dsA_cells. dsred. close_cells GA.
      - rewrite ESTRM. split; [apply (dout_munch _ mm mB L rest0 _ DOUT' ROOM MUs WMs); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
        split; [exact FR'|]. split; [exact STK'|]. split; [exact MU'|]. split; [exact WM'| eassumption]. }
    zstep. if_cases KX; zify_cond KX.
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
      unfold KINS, slowR in IH.
      eapply (IH Q (insl_st X mi) mi v11 v12 HI'); [rewrite EPL', PLn; lia| lia| lia| rewrite ESS'; lia| exact MI0| exact MI2| exact KEXIT| exact SI']. }
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_h _ LAY) as BKh. unfold blk_ok in BKh. pose proof (lo_p _ LAY) as BKp. unfold blk_ok in BKp.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUs.
  zs. zstep.
  if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
  -
    name_mem mS. clear MUf. tr_groups MUs WMf.
    eapply (FIN (set_strstart X (ds_strstart X + 1)) _ _ _ _ _ _ _ _ _ _ _ mS); [exact ZS| unfold dsA_cells; dsred; exact GA| | | exact FR| exact STK| exact MU| exact WM| eassumption].
    2:{ apply (dout_munch _ mA mS L rest0 _ DOUT ROOM MUs WMf). cbn [disjoint_from]. slia. }
    intros v k1' k2' k3' k4' k5' mm' MU2 WM2 GA2.
    replace (ds_strstart X + 1 <=? mi) with false by (symmetry; apply Z.leb_gt; lia).
    clear GA. tr_groups MU2 WM2.
    constructor; [do 5 eexists; exact GA2 | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  -
    name_mem mS.
    assert (GwinS : dwin mS L X) by (apply (dwin_munch mA mS L X _ Gwin MUs WMf); cbn [disjoint_from]; slia).
    assert (GprevS : dprev mS L X) by (apply (dprev_munch mA mS L X _ Gprev MUs WMf); cbn [disjoint_from]; slia).
    assert (GheadS : dhead mS L X) by (apply (dhead_munch mA mS L X _ Ghead MUs WMf); cbn [disjoint_from]; slia).
    clear Gwin Gprev Ghead MUs. rename GwinS into Gwin. rename GprevS into Gprev. rename GheadS into Ghead.
    pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mS) as MUg. pose proof (wmono_refl usegs mS) as WMg.
    open_u16 Gprev. open_u16 Ghead.
    pose proof (ln_prev _ LENS) as Lprev. pose proof (ln_head _ LENS) as Lhead.
    zs. gF. zs. zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX. gF.
    zs.
    ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + 3) ltac:(apply Rwb; lia).
    zs. zs. zs. zs. zs.
    rewrite (hash_mach X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3))) by lia.
    pose proof (update_hash_range X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3)) ltac:(lia)) as Rhv.
    remember (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3))) as h eqn:Eh.
    zstep. zstep. rewrite (shl32_shr31 h) by lia. zstep. zs.
    gF. zstep. zstep. zstep. gX. gF. zstep.
    assert (ALh : (dl_Ah L + 2 * h) mod 2 = 0) by (clear - BKh Rhv; Z.div_mod_to_equations; lia).
    first [rewrite (land1_mod2 _ ALh) | replace (2 * h + dl_Ah L) with (dl_Ah L + 2 * h) by lia; rewrite (land1_mod2 _ ALh)]. gF.
    zs. zs. zstep. try rewrite (Z.land_comm (ds_w_mask X) (ds_strstart X + 1)). zstep. zstep.
    rewrite ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite ?(Z.mul_comm _ 2).
    pose proof (LmatchModel.land_upper_both (ds_strstart X + 1) (ds_w_mask X) ltac:(lia) ltac:(lia)) as Rpi.
    remember (Z.land (ds_strstart X + 1) (ds_w_mask X)) as pi eqn:Epi.
    gF. zstep. zstep. zstep. gX. gF. zstep.
    assert (ALp : (dl_Ap L + 2 * pi) mod 2 = 0) by (clear - BKp Rpi; Z.div_mod_to_equations; lia).
    first [rewrite (land1_mod2 _ ALp) | replace (2 * pi + dl_Ap L) with (dl_Ap L + 2 * pi) by lia; rewrite (land1_mod2 _ ALp) | replace (dl_Ap L + pi * 2) with (dl_Ap L + 2 * pi) by lia; rewrite (land1_mod2 _ ALp)]. gF.
    pose proof (Rhb h ltac:(lia)) as Rhh.
    ld16 Ghead (ds_head X) 32768 (dl_Ah L) h ltac:(apply Rhb; lia).
    st16 Gprev (ds_prev X) 32768 (dl_Ap L) pi (arr_get (ds_head X) h) ltac:(reflexivity).
    gT.
    st16 Ghead (ds_head X) 32768 (dl_Ah L) h (wrap16 (ds_strstart X + 1)) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
    name_mem mB.
    tr_groups MUf WMf. tr_groups MUg WMg.
    subst h pi. replace (ds_strstart X + 3) with (ds_strstart X + 1 + 2) in * by lia.
    eapply (FIN (ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1)) _ _ _ _ _ _ _ _ _ _ _ mB); [exact ZS| unfold dsA_cells, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.ins_str; dsred; exact GA| | | exact FR| exact STK| exact MU| exact WM| eassumption].
    2:{ apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf). cbn [disjoint_from]. slia. }
    intros v k1' k2' k3' k4' k5' mm' MU2 WM2 GA2.
    replace (ds_strstart X + 1 <=? mi) with true by (symmetry; apply Z.leb_le; lia).
    clear GA.
    change (dprev mB L (ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1))) in Gprev.
    change (dhead mB L (ins_str (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1))) in Ghead.
    tr_groups MU2 WM2.
    unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.ins_str. constructor; [do 5 eexists; unfold dsA_cells; dsred; unfold dsA_cells, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.ins_str in GA2; dsred in GA2; exact GA2 | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
Qed.

Definition KA (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me X m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart X)) y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a230) fc None m' (seg_rom usegs)).

Lemma slow_dexit : forall (Q : machine_state -> Prop) (Xf : deflate_state) (sn se : Z)
    (y1 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me Xf m -> 0 <= sn < 2^32 -> 0 <= se < 2^32 ->
  (sn <> se -> SK L flush rest0 lo r fj F fc me Q Z_SLOW_HEAD (exit_st Xf)) ->
  (sn = se -> KA Q (exit_st Xf)) ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_strstart Xf + 1)) (wz sn) (wz se) y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a21c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI) Rsn Rse KH0 KA0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU. unfold SK, Z_SLOW_HEAD, slowR in KH0. unfold KA, slowR in KA0.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zstep. zs. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : SINV L flush rest0 lo r fj me (exit_st Xf) mB).
  { split; [split|].
    - exact ZS.
    - unfold exit_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - eapply (KH0 KB). exact SI'.
  - replace (wz (ds_strstart Xf + 1)) with (wz (ds_strstart (exit_st Xf))) by reflexivity.
    eapply (KA0 KB). exact SI'.
Qed.
End DIST2.
End Z_slow_dist2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_drep.Z_tr_rod OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_dist.Z_slow_dist1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_slow_dist.Z_slow_dist2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz DeflateBlk FillWinModel LmatchModel RefDeflFast1 RefDeflFastM RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.LmatchModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFastM OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflFast6 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section DIST.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Lemma slow_dist : forall (Q : machine_state -> Prop) (X : deflate_state)
    (y1 y5 y6 y7 y11 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r fj me X m ->
  strip_inv X -> dist_cond X = true -> sdist_ok 32768 X -> 1 <= ds_lookahead X <= 65536 -> ds_w_size X = 32768 -> ds_hash_size X = 32768 -> ds_lit_bufsize X = 16384 ->
  (snd (st_sdist X) = false -> SK L flush rest0 lo r fj F fc me Q Z_SLOW_HEAD (fst (st_sdist X))) ->
  (snd (st_sdist X) = true -> KA L flush rest0 lo r fj F fc me Q (fst (st_sdist X))) ->
  evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz (ds_match_length X)) y11 (wz (ds_prev_length X)) y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x19e94) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros SI SV DC (PLLA & SL3 & DD & _ & _) RLA WS HS LBS KH0 KA0.
  unfold dist_cond in DC. apply andb_prop in DC. destruct DC as [DC1 _]. apply Z.leb_le in DC1.
  pose proof SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *. rewrite HS in *. rewrite LBS in *.
  destruct (sdist_eq X DC1 PLLA ltac:(lia) SL3 ltac:(lia)) as [EF ES]. rewrite EF, ES in KH0, KA0. clear EF ES.
  eapply (slow_tdist1 L flush inp rest0 lo r fj F fc me CTX Q X); [exact SI| exact SV| exact DC1| exact RLA| exact WS| exact LBS|].
  unfold KT1. intros until m'. intros SI1.
  eapply (slow_tdist2 L flush inp rest0 lo r fj F fc me CTX Q (sdist1 X) (sdist_D X)); [exact SI1| | | | | | | | | | ].
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
  eapply (slow_ins L flush inp rest0 lo r fj F fc me CTX HFL (Z.to_nat (ds_prev_length X - 2)) Q T (ds_strstart X + ds_lookahead X - 3)); [exact TI| rewrite TPL; lia| lia| lia| rewrite TSS; lia| lia| lia|].
  intros until m'0. intros SIF.
  eapply (slow_dexit L flush inp rest0 lo r fj F fc me CTX Q _ (ds_sym_next (sdist1 X)) (ds_sym_end (sdist1 X))); [exact SIF| unfold sdist1; dsred; lia| unfold sdist1; dsred; lia| |].
  - intros NE. apply KH0. apply Z.eqb_neq. unfold sdist1 in NE. dsred in NE. exact NE.
  - intros EQ. apply KA0. apply Z.eqb_eq. unfold sdist1 in EQ. dsred in EQ. exact EQ.
Qed.
End DIST.
