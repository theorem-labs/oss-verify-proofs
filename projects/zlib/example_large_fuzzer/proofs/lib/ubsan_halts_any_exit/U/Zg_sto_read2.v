(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_adler32 Z_fw_slide Z_ukit Z_fw_model Zg_fw_model
     Z_readbuf Zg_adler32_iface Zg_readbuf Zg_defl_iface Zg_sto_ole Zg_sto_kit Zg_sto_head Zg_sto_emit Zg_sto_rdo Zg_sto_used Zg_sto_fill.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel ZChkAdl AdlerModel
     RefDeflStored1 RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflStored9 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_FINAL : Z := 0x18ca8.

Ltac join_x18 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode ?Lt None (TNode ?A ?o2 (TNode (TNode (TNode TEmpty (Some _) TEmpty) ?o10 ?B) ?o6 ?C))) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut usegs (fun ms' => ms' = MS (TNode Lt None (TNode A o2 (TNode (TNode (TNode TEmpty (Some v) TEmpty) o10 B) o6 C))) F (wz pcj) fc None m rom))
  end.

Lemma st_fillw_set : forall s n, 0 < n <= cs_avail_in (ds_strm s) -> ds_wrap s <> 2 ->
  let l := arr_slice (cs_input (ds_strm s)) (cs_next_in (ds_strm s)) n in
  let X4 := set_strm (set_window s (arr_upd (ds_window s) (ds_strstart s) l)) (rbn_strm s l n) in
  st_fillw s n = set_insert (set_strstart X4 (ds_strstart s + n)) (ins_add (ds_insert s) n (ds_w_size s)).
Proof.
  intros s n Hn W2. cbv zeta. unfold st_fillw, ins_add. replace (negb (n =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  rewrite (read_buf_eqn s (ds_strstart s) n n) by (first [unfold rb_len; symmetry; apply rb_len_eq; exact Hn | lia | exact W2]).
  reflexivity.
Qed.

Lemma rbn_out : forall s l n, cs_out_rev (rbn_strm s l n) = cs_out_rev (ds_strm s).
Proof. intros. unfold rbn_strm. destruct (ds_wrap s =? 1); reflexivity. Qed.

Section READ2.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HADL : adler32_stmt.

Definition KFIN (Q : machine_state -> Prop) (X : deflate_state) : Prop := TK10 L flush ai0 1 rest0 lo r F fc me Q Z_STO_FINAL (ds_strstart X) X.

Lemma sto_hw2 : forall (Q : machine_state -> Prop) (Y : deflate_state)
    (y1 y5 y6 y7 y9 y10 w11 y12 y13 y14 y15 y16 y17 y18 y20 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush rest0 lo r me Y m' -> 0 <= ds_strstart Y < 2^32 -> 0 <= ds_high_water Y < 2^64 ->
  bv_unsigned w11 mod 4294967296 = ds_strstart Y ->
  KFIN Q (hw_st Y) ->
  evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 y9 y10 w11 y12 y13 y14 y15 y16 y17 y18 y20 y28 y29 y30 y31)
                  F (wz Z_STO_FIN2) fc None m' (seg_rom usegs)).
Proof using CTX inp.
  intros until m'. intros INV RSTR RHW E11 K.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_FIN2, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. below_open BEL. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  open_DST ST. open_D GD. unfold sto_W, slow_W in MU. unfold KFIN, TK10 in K.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] m') as MUf. pose proof (wmono_refl usegs m') as WMf.
  pose proof (hw_st_facts Y) as (Hs & _).
  zs. zstep. zstep. rewrite E11. zstep. br_cases K1.
  -
    replace (wz (ds_strstart Y)) with (wz (ds_strstart (hw_st Y))) by (rewrite Hs; reflexivity).
    eapply K.
    unfold hw_st. replace (ds_high_water Y <? ds_strstart Y) with false by (symmetry; apply Z.ltb_ge; exact K1).
    split; [split; [exact ZS|]|].
    { constructor; [exact GA| exact GB| exact GC| eexists _, _, _, _, _; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]. }
    split; [exact DOUT|]. split; [exact RM|]. split; [unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
  - zs. name_mem mB.
    replace (wz (ds_strstart Y)) with (wz (ds_strstart (hw_st Y))) by (rewrite Hs; reflexivity).
    eapply K.
    unfold hw_st. replace (ds_high_water Y <? ds_strstart Y) with true by (symmetry; apply Z.ltb_lt; exact K1).
    tr_groups MUf WMf.
    split; [split; [first [exact ZS| eapply dzs_munch; [exact ZS| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|]|].
    { constructor; [exact GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY]. }
    split; [first [exact DOUT| eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|].
    split; [exact RM|]. split; [unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Variables (Q : machine_state -> Prop) (X3 : deflate_state) (have : Z).
Let n := fmin have (cs_avail_in (ds_strm X3)).
Hypothesis HV3 : so_inv X3.
Hypothesis TIE : din_tie inp X3.
Hypothesis WS : ds_w_size X3 = 32768.
Hypothesis WRAP : ds_wrap X3 <> 2.
Hypothesis RAI : cs_avail_in (ds_strm X3) < 2^31.
Hypothesis RHV : 0 <= have /\ ds_strstart X3 + have <= 65536.
Hypothesis K : KFIN Q (hw_st (st_fillw X3 n)).

Lemma sto_read2 : KRD2 L flush ai0 rest0 lo r F fc me Q X3 have.
Proof using K RHV RAI WRAP WS TIE HV3 n HADL CTX inp.
  unfold KRD2. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_RD2, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (tc_sp16 _ _ _ _ _ _ CTX) as SP16.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (lo_S _ LAY) as BKS. unfold blk_ok in BKS.
  pose proof (vi_str _ HV3) as Vstr. pose proof (vi_bs _ HV3) as Vbs. pose proof (vi_ins _ HV3) as Vins. pose proof (vi_hw _ HV3) as Vhw.
  pose proof (vi_ni _ HV3) as Vni. pose proof (vi_inlen _ HV3) as Vinl. pose proof (vi_ai _ HV3) as Vai. pose proof (vi_wrap _ HV3) as Vwr.
  pose proof (vi_ad _ HV3) as Vad. pose proof (vi_ti _ HV3) as Vti.
  pose proof TIE as [TIE1 TIE2]. rewrite TIE1, arr_len_of_list in Vinl. rewrite WS in Vstr, Vins.
  pose proof ST as STc. open_DST STc. open_A GA. pose proof ZS as ZSc. open_zs ZSc. unfold sto_W, slow_W in MU. unfold KFIN in K.
  zs. gF. zstep. al8 (dl_S L). gF. zs.
  zstep. join_x18 (wz n) 0x18c3c.
  { br_cases K1.
    - replace (wz n) with (wz have) by (f_equal; subst n; unfold fmin; destruct (Z.ltb_spec (cs_avail_in (ds_strm X3)) have); lia). apply evt_done. reflexivity.
    - zstep. replace (wz n) with (wz (cs_avail_in (ds_strm X3))) by (f_equal; subst n; unfold fmin; destruct (Z.ltb_spec (cs_avail_in (ds_strm X3)) have); lia).
      apply evt_done. reflexivity. }
  intros ms' ->.
  assert (RN : 0 <= n <= have /\ n <= cs_avail_in (ds_strm X3)) by (subst n; apply fmin_range; lia).
  zstep. br_cases K2.
  {
    assert (En : n = 0) by lia. rewrite En, st_fillw_0 in K.
    eapply (sto_hw2 Q X3); [exact INV| lia| lia| rewrite unsigned_lit by lia; apply Z.mod_small; lia| exact K]. }
  assert (RNp : 0 < n <= cs_avail_in (ds_strm X3)) by lia.
  pose proof (st_fillw_facts X3 n RNp) as [EFS EFH].
  zs. zstep. zstep. rewrite (Z.mod_small (ds_strstart X3)) by lia. zstep. gF. zstep. zstep. zstep. gX. zstep.
  replace (wz (ds_strstart X3 + dl_Aw L)) with (wz (dl_Aw L + ds_strstart X3)) by (f_equal; lia).
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -112)) = bv_unsigned (r_sp r) + -112) by (apply unsigned_lit; lia).
  pose proof (sto_din _ _ _ _ _ _ CTX m' MU) as DIN. pose proof (ln_win _ LENS) as LNW0.
  clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY0 ZSc. unfold dout in DOUT.
  pose proof (outv_length rest0 (ds_strm X3) (unbox _ RM)) as OL.
  zstep. call (read_buf_win_spec HADL L X3 inp (Z.of_nat (length rest0)) lo n (ds_strstart X3) (dl_Aw L + ds_strstart X3)).
  1:{ split; [exact ZS| exact ST]. } 1:{ exact DIN. } 1:{ exact TIE. } 1:{ exact MI. }
  1:{ rewrite ESP. exact STK. } 1:{ unfold Z_READBUF_STACK. rewrite ESP. lia. } 1:{ rewrite ESP. clear - SP16 RSP LOsp. Z.div_mod_to_equations. lia. }
  1:{ rewrite ESP. eapply dlay_below_lower; [exact BEL| lia]. } 1:{ exact IO. } 1:{ exact LNW0. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ exact Vwr. } 1:{ exact WRAP. } 1:{ intros W1. apply Vad. lia. } 1:{ exact Vni. } 1:{ lia. } 1:{ exact Vinl. } 1:{ exact Vti. } 1:{ reflexivity. }
  name_mem m2. rewrite ESP in PC. rename PC into STK2. clear DIN ZS ST.
  rewrite (read_buf_eqn X3 (ds_strstart X3) n n) in PC0 by (first [unfold rb_len; symmetry; apply rb_len_eq; exact RNp | lia | exact WRAP]).
  rewrite fst_pr in PC0.
  remember (arr_slice (cs_input (ds_strm X3)) (cs_next_in (ds_strm X3)) n) as l eqn:El.
  destruct PC0 as [ZS4 ST4]. pose proof ST4 as STc. open_DST STc. open_A GA. open_D GD. unfold dsA_cells in GA. unfold dsD_cells in GD. dsred in GA. dsred in GD.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] m2) as MUf. pose proof (wmono_refl usegs m2) as WMf.
  pose proof (ins_add_eq (ds_insert X3) n (ds_w_size X3) ltac:(lia) ltac:(lia) ltac:(lia)) as [EIA RIA].
  zs. zs. zs. zstep. zs. zs.
  remember (if n <? ds_w_size X3 - ds_insert X3 then n else ds_w_size X3 - ds_insert X3) as mn eqn:Emn.
  zstep. join_x18 (wz mn) 0x18c8c.
  { br_cases K3.
    - replace (wz mn) with (wz n) by (f_equal; rewrite Emn; destruct (Z.ltb_spec n (ds_w_size X3 - ds_insert X3)); lia). apply evt_done. reflexivity.
    - zstep. replace (wz mn) with (wz (ds_w_size X3 - ds_insert X3)) by (f_equal; rewrite Emn; destruct (Z.ltb_spec n (ds_w_size X3 - ds_insert X3)); lia).
      apply evt_done. reflexivity. }
  intros ms' ->.
  zs. zs. name_mem mB. tr_groups MUf WMf.
  eapply (sto_hw2 Q (st_fillw X3 n)); [| rewrite EFS; lia | rewrite EFH; lia | rewrite EFS, unsigned_lit by lia; apply Z.mod_small; lia | exact K].
  rewrite (st_fillw_set X3 n RNp WRAP). cbv zeta. rewrite <- El, EIA.
  split; [split|].
  - dsred. dsred in ZS4. first [exact ZS4| eapply dzs_munch; [exact ZS4| exact MUf| exact WMf| cbn [disjoint_from]; slia]].
  - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD
                 | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY].
  - split; [unfold dout; dsred; replace (outv rest0 (rbn_strm X3 l n)) with (outv rest0 (ds_strm X3)) by (unfold outv; rewrite rbn_out; reflexivity); exact DOUT|].
    split; [constructor; dsred; rewrite rbn_out; exact (unbox _ RM)|].
    split; [exact FR|]. split; [exact STK2|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End READ2.
