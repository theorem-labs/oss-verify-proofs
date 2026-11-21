(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_tr_emit
     Zg_defl_iface Zg_sto_model Zg_sto_ole Zg_sto_kit Zg_sto_head Zg_sto_emit Zg_sto_read2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel TrSmallModel
     RefDeflFast1 RefDeflFastM RefDeflStored1 RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflStored9 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_COND2 : Z := 0x186c0.
Definition Z_STO_EMITF : Z := 0x186f0.

Lemma hdr_mach : forall x, 0 <= x < 2^30 -> Z.shiftr (Z.shiftl x 29 mod 18446744073709551616) 32 = x / 2^3.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^35 * 2^29); apply Z.mul_lt_mono_pos_r; lia).
  change (2^32) with (2^29 * 2^3). rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma cond2_mach : forall flush a b, 0 <= flush <= 5 -> 0 <= a -> 0 <= b ->
  Z.lor (Z.b2z ((flush + -4) mod 18446744073709551616 <? 1)) (Z.b2z (0 <? Z.lxor a b)) = (if negb (a =? b) || (flush =? 4) then 1 else 0).
Proof.
  intros flush a b Hf Ha Hb.
  assert (E1 : ((flush + -4) mod 18446744073709551616 <? 1) = (flush =? 4)).
  { assert (C : flush = 0 \/ flush = 1 \/ flush = 2 \/ flush = 3 \/ flush = 4 \/ flush = 5) by lia.
    destruct C as [-> |[-> |[-> |[-> |[-> | ->]]]]]; reflexivity. }
  rewrite E1.
  assert (E2 : (0 <? Z.lxor a b) = negb (a =? b)).
  { pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)) as N.
    destruct (Z.eqb_spec a b) as [E|NE].
    - subst. rewrite Z.lxor_nilpotent. reflexivity.
    - cbn [negb]. apply Z.ltb_lt. destruct (Z.eq_dec (Z.lxor a b) 0) as [Z0|Z0]; [|lia]. exfalso. apply NE. apply (proj1 (Z.lxor_eq_0_iff a b)). exact Z0. }
  rewrite E2. destruct (a =? b), (flush =? 4); reflexivity.
Qed.

Lemma cond2_mach' : forall flush a b, 0 <= a -> 0 <= b ->
  Z.lor (if flush =? 4 then 1 else 0) (Z.b2z (0 <? Z.lxor a b)) = (if negb (a =? b) || (flush =? 4) then 1 else 0).
Proof.
  intros flush a b Ha Hb.
  assert (E2 : (0 <? Z.lxor a b) = negb (a =? b)).
  { pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)) as N.
    destruct (Z.eqb_spec a b) as [E|NE].
    - subst. rewrite Z.lxor_nilpotent. reflexivity.
    - cbn [negb]. apply Z.ltb_lt. destruct (Z.eq_dec (Z.lxor a b) 0) as [Z0|Z0]; [|lia]. exfalso. apply NE. apply (proj1 (Z.lxor_eq_0_iff a b)). exact Z0. }
  rewrite E2. destruct (a =? b), (flush =? 4); reflexivity.
Qed.

Ltac join_x19 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode (TNode (TNode ?LL ?o3 (TNode (TNode TEmpty (Some _) TEmpty) ?o11 ?C)) ?o1 ?R5) None ?R) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut psegs (fun ms' => ms' = MS (TNode (TNode (TNode LL o3 (TNode (TNode TEmpty (Some v) TEmpty) o11 C)) o1 R5) None R) F (wz pcj) fc None m rom))
  end.

Section FIN.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.
Hypothesis HTSB : tr_stored_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.

Lemma sto_epi8 : forall (lz : Z) (dF : deflate_state) (code : Z)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush ai0 lz rest0 lo r me dF m' ->
  evt psegs (slow_post_gen r F fc L dF code inp rest0 lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -160)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 (wz code) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
        F (wz Z_STO_EPI) fc None m' (seg_rom psegs)).
Proof using CTX.
  intros until m'. intros (DR & DOUT & _ & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_EPI.
  pose proof (sto_din _ _ _ _ _ _ CTX m' MU) as DIN. unfold sto_W, slow_W in MU.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 13 zs.
  release_frame FR STK (bv_unsigned (r_sp r)). zs. zs.
  apply evt_done. unfold slow_post_gen. do 14 eexists. exists m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
  split; [exact DR|]. split; [exact DIN| exact DOUT].
Qed.

Lemma sto_epi8bu : forall (lz : Z) (dF : deflate_state) (code : Z)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush ai0 lz rest0 lo r me dF m' ->
  evt psegs (slow_post_gen r F fc L dF code inp rest0 lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -160)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 (wz code) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22
             (wz (dl_As L + 5928)) y24 y25 y26 y27 y28 y29 y30 y31)
        F (wz Z_STO_EPIBU) fc None m' (seg_rom psegs)).
Proof using CTX.
  intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_EPIBU.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. below_open BEL. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  open_DST ST. open_D GD. unfold sto_W, slow_W in MU.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] m') as MUf. pose proof (wmono_refl psegs m') as WMf.
  zs. zs. zs. name_mem mB.
  eapply (sto_epi8 lz).
  tr_groups MUf WMf.
  split; [split; [first [exact ZS| eapply dzs_munch; [exact ZS| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|]|].
  { constructor; [exact GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]. }
  split; [first [exact DOUT| eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|].
  split; [exact RM|]. split; [eexists; unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Ltac fin_tail :=
  zstep; let KZ := fresh "KZ" in br_cases KZ; rewrite ?unsigned_lit in KZ by lia;
  [ zstep; lazymatch goal with |- context [slow_post_gen _ _ _ _ _ (?lst * 2)] => replace (lst * 2) with 0 by lia end; eapply (sto_epi8 1)
  | zstep; lazymatch goal with |- context [slow_post_gen _ _ _ _ _ (?lst * 2)] => replace (lst * 2) with 2 by lia end; eapply (sto_epi8bu 1) ].

Variables (X : deflate_state).
Let Q := slow_post_gen r F fc L (fst (st_final X flush)) (bs_code (snd (st_final X flush))) inp rest0 lo me.
Let left := ds_strstart X - ds_block_start X.
Hypothesis HV : so_inv X.
Hypothesis WS : ds_w_size X = 32768.
Hypothesis PBS : ds_pending_buf_size X = 65536.
Hypothesis LBS : ds_lit_bufsize X = 16384.
Hypothesis RAI : cs_avail_in (ds_strm X) < 2^31.
Hypothesis RAO : 0 <= cs_avail_out (ds_strm X) < 2^31.
Hypothesis FOK : so_final_ok X flush.
Hypothesis RMF : Box (length (cs_out_rev (ds_strm (fst (st_final X flush)))) <= length rest0)%nat.

Lemma fin_emitf : forall (y1 y5 y6 y7 y9 y10 y11 y15 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush ai0 1 rest0 lo r me X m' -> fin_cond X flush = true ->
  evt psegs Q (MS (stoR L r y1 y5 y6 y7 y9 y10 y11 (wz (ds_block_start X)) (wz (t_have X)) (wz left) y15 (wz flush) y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31)
                  F (wz Z_STO_EMITF) fc None m' (seg_rom psegs)).
Proof using RMF FOK RAO RAI LBS PBS WS HV HTFB HTSB HFL CTX.
  intros until m'. intros INV FC.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_EMITF, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (vi_str _ HV) as Vstr. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_bv _ HV) as Vbv. pose proof (vi_ai _ HV) as Vai. rewrite WS in Vstr.
  destruct (t_have_eq X Vbv ltac:(lia)) as (ETH & RTH & _).
  assert (ELEFT : wrap32 (ds_strstart X - ds_block_start X) = left) by (subst left; rewrite wrap32_mod; apply Z.mod_small; lia).

  unfold Q. rewrite st_final_eq, FC, fst_pr, snd_pr.
  assert (EFL : fin_len X = (if left <? t_have X then left else t_have X)).
  { unfold fin_len, MIN. rewrite ELEFT. destruct (Z.ltb_spec (t_have X) left), (Z.ltb_spec left (t_have X)); lia. }
  assert (ELAST : fin_last X flush = (if (flush =? Z_FINISH) && (cs_avail_in (ds_strm X) =? 0) && (fin_len X =? left) then 1 else 0)).
  { unfold fin_last. rewrite ELEFT. reflexivity. }
  unfold so_final_ok in FOK. cbv zeta in FOK. rewrite LBS in FOK. change (16384 * 4) with 65536 in FOK.
  remember (fin_last X flush) as last eqn:Elast0.
  remember (fin_len X) as len eqn:Elen0.
  assert (RL : 0 <= last <= 1) by (rewrite ELAST; destruct (_ && _); lia).
  pose proof ST as ST0. open_DST ST. open_A GA. open_zs ZS. unfold sto_W, slow_W in MU.

  zs. zstep. zstep. join_x19 (wz len) 0x18700.
  { br_cases K1.
    - replace (wz len) with (wz left) by (f_equal; rewrite EFL; destruct (Z.ltb_spec left (t_have X)); lia). apply evt_done. reflexivity.
    - zstep. replace (wz len) with (wz (t_have X)) by (f_equal; rewrite EFL; destruct (Z.ltb_spec left (t_have X)); lia). apply evt_done. reflexivity. }
  intros ms' ->.
  assert (RLEN : 0 <= len <= left /\ len <= t_have X) by (rewrite EFL; destruct (Z.ltb_spec left (t_have X)); lia).

  assert (KTSB : forall (v10 v11 v13 : word) (mA : mem), mA = m' ->
    evt psegs (slow_post_gen r F fc L (st_femit X flush) (bs_code (if negb (last =? 0) then finish_started else need_more)) inp rest0 lo me)
      (MS (stoR L r y1 y5 y6 y7 (wz last) v10 v11 (wz (ds_block_start X)) v13 (wz left) y15 (wz flush) y17
               y18 (wz len) y20 y21 y22 y27 y28 y29 y30 y31)
          F (wz 0x18718) fc None mA (seg_rom psegs))).
  2:{ zstep. zstep. br_cases K2.
      -
        zstep. replace (flush =? Z_FINISH) with false in ELAST by (symmetry; apply Z.eqb_neq; unfold Z_FINISH; lia). cbn [andb] in ELAST.
        rewrite ELAST in KTSB. rewrite ELAST. apply (KTSB _ _ _ _ eq_refl).
      - replace (flush =? Z_FINISH) with true in ELAST by (symmetry; apply Z.eqb_eq; unfold Z_FINISH; lia). cbn [andb] in ELAST.
        zstep. zs. zstep. br_cases K3.
        +
          replace (cs_avail_in (ds_strm X) =? 0) with true in ELAST by (symmetry; apply Z.eqb_eq; lia). cbn [andb] in ELAST.
          zs. zstep. zstep. zstep. rewrite ELAST in KTSB. rewrite ELAST.
          replace (wz (Z.lxor (Z.b2z (t_have X <? left)) 1)) with (wz (if len =? left then 1 else 0)).
          2:{ f_equal. rewrite EFL. destruct (Z.ltb_spec (t_have X) left); destruct (Z.ltb_spec left (t_have X)); try lia.
              - replace (t_have X =? left) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
              - rewrite Z.eqb_refl. reflexivity.
              - replace (t_have X =? left) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
          apply (KTSB _ _ _ _ eq_refl).
        + replace (cs_avail_in (ds_strm X) =? 0) with false in ELAST by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ELAST.
          zstep. rewrite ELAST in KTSB. rewrite ELAST. apply (KTSB _ _ _ _ eq_refl). }
  intros v10 v11 v13 mA ->. unfold stoR, stoR7.

  destruct (FOK FC) as (BI0 & RP1 & FPOK). clear FOK.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -160)) = bv_unsigned (r_sp r) + -160) by (apply unsigned_lit; lia).
  unfold dout in DOUT. pose proof (outv_length rest0 (ds_strm X) (unbox _ RM)) as OL.

  zstep. zstep. zstep. zstep. zstep.
  zstep. call (HTSB L X (Some (ds_block_start X)) len last lo).
  1:{ exact ST0. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. eapply dlay_below_lower; [exact BEL| lia]. }
  1:{ exact BI0. } 1:{ exact RP1. } 1:{ intros _ C; discriminate C. } 1:{ cbn [fb_buf_ok]. lia. } 1:{ lia. } 1:{ exact RL. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem m1. rewrite ESP in PC. rename PC into STK1. clear ST0. try clear GA. try clear GB. try clear GC. try clear GD. try clear Glt. try clear Gdt. try clear Gbt. try clear Gblc. try clear Gheap. try clear Gdep. try clear Gwin. try clear Gprev. try clear Ghead. try clear Gpend. try clear LENS. try clear LAY0.
  assert (HX1 : exists X1, X1 = tr_stored_block X (Some (ds_block_start X)) len last) by (eexists; reflexivity). destruct HX1 as [X1 EX1].
  pose proof (sb_keep X (Some (ds_block_start X)) len last) as KK. cbv zeta in KK. rewrite <- EX1 in KK, RP1, FPOK, POST. destruct KK as (K1s & K1w & K1ws & K1hs & K1lbs & K1bs & K1str).
  open_DST POST. open_A GA. rewrite K1bs in GA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m1) as MUf. pose proof (wmono_refl psegs m1) as WMf.

  zstep. zstep. zstep. zstep. zs. zstep. name_mem mB.
  assert (HX2 : exists X2, X2 = set_block_start X1 (ds_block_start X1 + len)) by (eexists; reflexivity). destruct HX2 as [X2 EX2].
  rewrite <- EX2 in FPOK.
  assert (K2s : ds_strm X2 = ds_strm X1) by (rewrite EX2; reflexivity).
  tr_groups MUf WMf.
  assert (ST2 : DST mB L X2).
  { rewrite EX2, K1bs.
    constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY]. }
  clear GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf LAY0 LENS.

  destruct FPOK as [BI2 FPK]. cbv zeta in FPK. destruct FPK as (RP3 & RP3' & RPB3 & RPO3 & RPOL3 & RTO3).
  zstep. clear GA. call (HTFB L X2).
  1:{ exact ST2. } 1:{ assumption. } 1:{ exact BI2. } 1:{ exact RPB3. } 1:{ reflexivity. }
  name_mem mC. clear ST2.
  assert (HX3 : exists X3, X3 = tr_flush_bits X2) by (eexists; reflexivity). destruct HX3 as [X3 EX3].
  pose proof (bits_keep X2) as KK. cbv zeta in KK. rewrite <- EX3 in KK, RP3, RP3', RPB3, RPO3, RPOL3, RTO3, POST.
  destruct KK as (K3s & K3w & K3ws & K3hs & K3lbs & K3bs & K3str & K3wr & K3po).
  assert (ES : ds_strm X3 = ds_strm X) by (rewrite K3s, K2s; exact K1s).

  assert (EF : st_femit X flush = (if fp_len X3 =? 0 then X3 else fp_tail X3 (fp_len X3))).
  { unfold st_femit. cbv zeta. rewrite <- Elen0, <- Elast0, <- EX1, <- EX2, flush_pending_eq. cbv zeta. rewrite <- EX3. reflexivity. }
  unfold Q in RMF |- *. rewrite st_final_eq, FC, fst_pr in RMF. rewrite EF in RMF |- *. clear EF.
  assert (EL : fp_len X3 = if cs_avail_out (ds_strm X) <? ds_pending X3 then cs_avail_out (ds_strm X) else ds_pending X3).
  { unfold fp_len. rewrite ES, wrap32_id by lia. reflexivity. }
  revert RMF RPOL3 EL. generalize (fp_len X3) as flen. intros flen RMF RPOL3 EL.
  open_DST POST. open_A GA.
  pose proof (munch_refl [(dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] mC) as MUf.
  pose proof (wmono_refl psegs mC) as WMf.
  zs. zs. zstep.
  assert (FL : 0 <= flen /\ flen <= cs_avail_out (ds_strm X) /\ flen <= ds_pending X3) by (destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X3)); lia).
  assert (ECODE : bs_code (if negb (last =? 0) then finish_started else need_more) = last * 2).
  { destruct (Z.eq_dec last 0) as [E|E]; [rewrite E; reflexivity|]. replace last with 1 by lia. reflexivity. }
  rewrite ECODE.

  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - replace (cs_avail_out (ds_strm X) <? ds_pending X3) with false in EL by (symmetry; apply Z.ltb_ge; lia).
      replace (wz (ds_pending X3)) with (wz flen) by (f_equal; lia). apply evt_done. reflexivity.
    - zstep. apply evt_done. replace flen with (cs_avail_out (ds_strm X)) by (rewrite EL; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X3)); lia).
      reflexivity. }
  intros ms' ->. clear EL.
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  -
    replace (flen =? 0) with true in RMF |- * by (symmetry; apply Z.eqb_eq; lia).
    fin_tail. all: split; [split|];
    [ exists zp1, zp2, zp3, zresv; rewrite ES; exact ZS
    | constructor; [eexists _, _, _, _, _; exact GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]
    | split; [unfold dout; rewrite ES; exact DOUT|]; split; [exact RMF|]; split; [eexists; exact FR|]; split; [exact STK1|];
      split; [exact MU|]; split; [exact WM| assumption] ].
  -
    replace (flen =? 0) with false in RMF |- * by (symmetry; apply Z.eqb_neq; lia).
    open_pend Gpend. pose proof (ln_pend _ LENS) as LNP.
    do 4 zstep. rewrite ?Z.mod_small by lia.
    remember (length (cs_out_rev (ds_strm X))) as k eqn:Ek.
    assert (KL : (k + Z.to_nat flen <= length rest0)%nat).
    { pose proof (unbox _ RMF) as R4. unfold fp_tail in R4. cbv zeta in R4. rewrite ES in R4.
      destruct (ds_pending X3 - flen =? 0); dsred in R4; rewrite cs_emit_out_len, arr_slice_length', <- Ek in R4; lia. }
    pose proof (u8arr_sub_bytes _ (dl_Ab L) _ (Z.to_nat (ds_pending_out X3)) (Z.to_nat flen) Gpend ltac:(rewrite av8_length; lia)) as SRC.
    rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
    assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_pending_buf X3) (ds_pending_out X3) flen)) = Z.to_nat flen)
      by (rewrite length_map; apply arr_slice_length').
    destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat flen) DOUT ltac:(rewrite OL; lia)) as (O1 & O2 & O3). clear DOUT.
    assert (LO1 : length (firstn k (outv rest0 (ds_strm X))) = k) by (rewrite length_firstn, OL; lia).
    assert (LO3 : length (skipn (k + Z.to_nat flen) (outv rest0 (ds_strm X))) = (length rest0 - (k + Z.to_nat flen))%nat) by (rewrite length_skipn, OL; lia).
    call (memcpy_Z (dl_NO L + Z.of_nat k) (dl_Ab L + ds_pending_out X3) flen).
    1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat flen) LO1 O1 PC O3) as OUT.
    fold (zb8 (arr_slice (ds_pending_buf X3) (ds_pending_out X3) flen)) in OUT.
    rewrite <- (arr_slice_length' (ds_pending_buf X3) (ds_pending_out X3) flen) in OUT. rewrite Ek in OUT.
    rewrite <- outv_emit in OUT by (rewrite <- Ek, arr_slice_length'; exact KL).
    assert (OL' : length (outv rest0 (cs_emit (ds_strm X) (arr_slice (ds_pending_buf X3) (ds_pending_out X3) flen))) = length rest0).
    { apply outv_length. rewrite cs_emit_out_len, arr_slice_length', <- Ek. lia. }
    clear O1 O3 PC POST SRC LSRC LO1 LO3.
    do 16 zs.
    if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    +
      tr_groups MUf WMf. fin_tail. all:
      (unfold fp_tail; cbv zeta; replace (ds_pending X3 - flen =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
       emit_close ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY OUT ES Ek FR STK1 MU WM KL).
    +
      do 2 zs. tr_groups MUf WMf. fin_tail. all:
      (unfold fp_tail; cbv zeta; replace (ds_pending X3 - flen =? 0) with true by (symmetry; apply Z.eqb_eq; lia);
       emit_close ZS GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY OUT ES Ek FR STK1 MU WM KL).
Qed.

Lemma sto_final : KFIN L flush ai0 rest0 lo r F fc me Q X.
Proof using RMF FOK RAO RAI LBS PBS WS HV left HTFB HTSB HFL CTX.
  unfold KFIN. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_FINAL, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (vi_str _ HV) as Vstr. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_bv _ HV) as Vbv. pose proof (vi_ai _ HV) as Vai. rewrite WS in Vstr.
  pose proof (sb_hdr_eq X Vbv) as [EH RH].
  destruct (t_have_eq X Vbv ltac:(lia)) as (ETH & RTH & _). rewrite PBS in ETH.
  replace (65536 - (ds_bi_valid X + 42) / 2 ^ 3 <? 65536) with true in ETH by (symmetry; apply Z.ltb_lt; lia).
  assert (ETH' : t_have X = ds_pending_buf_size X - (ds_bi_valid X + 42) / 2 ^ 3) by (rewrite PBS; exact ETH).
  pose proof (t_mb_eq X ltac:(lia)) as EMB. rewrite WS in EMB. replace (t_have X <=? 32768) with false in EMB by (symmetry; apply Z.leb_gt; lia).
  open_DST ST. open_A GA. open_D GD. open_zs ZS. unfold sto_W, slow_W in MU.
  zs. zstep. zs. zs. rewrite hdr_srlw by lia. rewrite Z.shiftr_div_pow2 by lia. zstep.
  change (2 ^ 3) with 8 in *.
  replace (wz (ds_pending_buf_size X - (ds_bi_valid X + 42) / 8)) with (wz (t_have X)) by (rewrite ETH'; reflexivity).
  zstep. zs. zstep. br_cases K1; [| exfalso; clear - K1 PBS RH RTH ETH; lia].
  zs. zstep. br_cases K2; [| exfalso; clear - K2 ETH RH WS RTH PBS; lia].
  zstep. zs. fold left. zstep. br_cases K3.
  -
    assert (EFC : fin_cond X flush = ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) && (cs_avail_in (ds_strm X) =? 0))).
    { unfold fin_cond. cbv zeta. rewrite EMB. subst left. rewrite wrap32_mod, Z.mod_small by lia.
      replace (32768 <=? ds_strstart X - ds_block_start X) with false by (symmetry; apply Z.leb_gt; lia). cbn [orb].
      replace (ds_strstart X - ds_block_start X <=? t_have X) with true by (symmetry; apply Z.leb_le; lia). rewrite Bool.andb_true_r. reflexivity. }
    assert (KNO : forall (v11 v15 v16 : word), fin_cond X flush = false ->
      evt psegs Q (MS (stoR L r y1 y5 y6 y7 y9 (wz 0) v11 (wz (ds_block_start X)) (wz (t_have X)) (wz left) v15 v16 y17
                       y18 y19 y20 y21 y22 y27 y28 y29 y30 y31) F (wz Z_STO_EPI) fc None m' (seg_rom psegs))).
    { intros v11 v15 v16 NFC. unfold stoR, stoR7. unfold Q. rewrite st_final_eq, NFC, fst_pr, snd_pr. apply (sto_epi8 1). exact INV. }
    zstep. zstep. br_cases K4.
    {   apply KNO. rewrite EFC. replace (flush =? Z_NO_FLUSH) with true by (symmetry; apply Z.eqb_eq; unfold Z_NO_FLUSH; lia).
      rewrite Bool.andb_false_r. reflexivity. }
    zs. zstep. zstep. zstep. zs. zstep.
    rewrite Z.add_0_r, (Z.mod_small (ds_strstart X)) by lia.
    rewrite (cond2_mach' flush (ds_strstart X) (ds_block_start X)) by lia.
    assert (ELB : (ds_strstart X =? ds_block_start X) = (left =? 0)).
    { subst left. destruct (Z.eqb_spec (ds_strstart X) (ds_block_start X)), (Z.eqb_spec (ds_strstart X - ds_block_start X) 0); try reflexivity; lia. }
    rewrite ELB. replace (flush =? Z_NO_FLUSH) with false in EFC by (symmetry; apply Z.eqb_neq; unfold Z_NO_FLUSH; lia). unfold Z_FINISH in EFC.
    destruct (negb (left =? 0) || (flush =? 4)) eqn:EB; cbn [negb andb] in EFC.
    2:{ zstep. br_cases K5; [| exfalso; clear - K5; cbn in K5; lia]. apply KNO. exact EFC. }
    zstep. br_cases K5; [exfalso; clear - K5; cbn in K5; lia|].
    zstep. zs. zstep. br_cases K6.
    + zstep. apply KNO. rewrite EFC. apply Z.eqb_neq. lia.
    + eapply fin_emitf; [exact INV|]. rewrite EFC. apply Z.eqb_eq. lia.
  -
    zstep. eapply fin_emitf; [exact INV|].
    unfold fin_cond. cbv zeta. rewrite EMB. subst left. rewrite wrap32_mod, Z.mod_small by lia.
    replace (32768 <=? ds_strstart X - ds_block_start X) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
End FIN.
