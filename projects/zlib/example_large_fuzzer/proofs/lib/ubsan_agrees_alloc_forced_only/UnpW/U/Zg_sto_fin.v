(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_tr_emit Z_ukit Z_flushpend Zg_adler32_iface Zg_readbuf Zg_defl_iface Zg_sto_ole Zg_sto_kit Zg_sto_head Zg_sto_emit Zg_sto_read2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel TrSmallModel DeflateSafe. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored2 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflStored9 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_EMITF : Z := 0x18d3c.
Definition Z_STO_TSBF : Z := 0x18d84.

Lemma hdr_mach : forall x, 0 <= x < 2^30 -> Z.shiftr (Z.shiftl x 29 mod 18446744073709551616) 32 = x / 2^3.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (split; [lia|]; change 18446744073709551616 with (2^35 * 2^29); apply Z.mul_lt_mono_pos_r; lia).
  change (2^32) with (2^29 * 2^3). rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cond2_machU : forall flush left, 0 <= flush <= 5 -> 0 <= left ->
  Z.lor (Z.b2z ((flush + -4) mod 18446744073709551616 <? 1)) (Z.b2z (0 <? left)) = (if negb (left =? 0) || (flush =? 4) then 1 else 0).
Proof.
  intros flush left Hf Hl.
  assert (E1 : ((flush + -4) mod 18446744073709551616 <? 1) = (flush =? 4)).
  { assert (C : flush = 0 \/ flush = 1 \/ flush = 2 \/ flush = 3 \/ flush = 4 \/ flush = 5) by lia.
    destruct C as [-> |[-> |[-> |[-> |[-> | ->]]]]]; reflexivity. }
  rewrite E1. destruct (Z.eqb_spec left 0) as [E|NE].
  - rewrite E. cbn [Z.ltb Z.b2z negb orb]. destruct (flush =? 4); reflexivity.
  - replace (0 <? left) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb orb Z.b2z]. destruct (flush =? 4); reflexivity.
Qed.

Lemma cond2_mach14 : forall flush left, 0 <= left ->
  Z.lor (if flush =? 4 then 1 else 0) (Z.b2z (0 <? left)) = (if negb (left =? 0) || (flush =? 4) then 1 else 0).
Proof.
  intros flush left Hl. destruct (Z.eqb_spec left 0) as [E|NE].
  - rewrite E. cbn [Z.ltb Z.b2z negb orb]. destruct (flush =? 4); reflexivity.
  - replace (0 <? left) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb orb Z.b2z]. destruct (flush =? 4); reflexivity.
Qed.

(* [comment removed for export] *)
Ltac join_x18 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode ?Lt None (TNode ?A ?o2 (TNode (TNode (TNode TEmpty (Some _) TEmpty) ?o10 ?B) ?o6 ?C))) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut usegs (fun ms' => ms' = MS (TNode Lt None (TNode A o2 (TNode (TNode (TNode TEmpty (Some v) TEmpty) o10 B) o6 C))) F (wz pcj) fc None m rom))
  end.

Section FIN.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.
Hypothesis HTSB : tr_stored_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.

(* [comment removed for export] *)
Lemma sto_epi9 : forall (lz : Z) (dF : deflate_state) (code : Z)
    (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y20 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush rest0 lo r me dF m' ->
  evt usegs (slow_post_gen r F fc L dF code inp rest0 lo me)
    (MS (stoR L flush ai0 lz r y1 y5 y6 y7 y9 (wz code) y11 y12 y13 y14 y15 y16 y17 y18 y20 y28 y29 y30 y31)
        F (wz Z_STO_EPI) fc None m' (seg_rom usegs)).
Proof using CTX.
  intros until m'. intros INV. pose proof (sto_epi L flush ai0 inp rest0 lo r F fc me CTX lz dF code) as E. unfold TK10 in E. apply E. exact INV.
Qed.

Lemma sto_epi9bu : forall (lz : Z) (dF : deflate_state) (code : Z)
    (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y18 y20 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush rest0 lo r me dF m' ->
  evt usegs (slow_post_gen r F fc L dF code inp rest0 lo me)
    (MS (stoR L flush ai0 lz r y1 y5 y6 y7 y9 (wz code) y11 y12 y13 y14 y15 y16 y17 y18 y20 y28 y29 y30 y31)
        F (wz Z_STO_EPIBU) fc None m' (seg_rom usegs)).
Proof using CTX.
  intros until m'. intros INV. pose proof (sto_epi_bu L flush ai0 inp rest0 lo r F fc me CTX lz dF code) as E. unfold TK10 in E. apply E. exact INV.
Qed.

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

(* [comment removed for export] *)
Lemma fin_emitf : forall (y1 y5 y6 y7 y9 y10 y15 y16 y17 y18 y20 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush rest0 lo r me X m' -> fin_cond X flush = true ->
  evt usegs Q (MS (stoR L flush ai0 1 r y1 y5 y6 y7 y9 y10 (wz (t_have X)) (wz (ds_block_start X)) (wz left) (wz left) y15 y16 y17 y18 y20 y28 y29 y30 y31)
                  F (wz Z_STO_EMITF) fc None m' (seg_rom usegs)).
Proof using RMF FOK RAO RAI LBS PBS WS HV HTFB HTSB HFL CTX.
  intros until m'. intros INV FC.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_EMITF, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (lo_S _ LAY) as BKS. unfold blk_ok in BKS.
  pose proof (vi_str _ HV) as Vstr. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_bv _ HV) as Vbv. pose proof (vi_ai _ HV) as Vai. rewrite WS in Vstr.
  destruct (t_have_eq X Vbv ltac:(lia)) as (ETH & RTH & _).
  assert (ELEFT : wrap32 (ds_strstart X - ds_block_start X) = left) by (subst left; rewrite wrap32_mod; apply Z.mod_small; lia).
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  zs. zstep. join_x18 (wz len) 0x18d48.
  { br_cases K1.
    - replace (wz len) with (wz (t_have X)) by (f_equal; rewrite EFL; destruct (Z.ltb_spec left (t_have X)); lia). apply evt_done. reflexivity.
    - zstep. replace (wz len) with (wz left) by (f_equal; rewrite EFL; destruct (Z.ltb_spec left (t_have X)); lia). apply evt_done. reflexivity. }
  intros ms' ->.
  assert (RLEN : 0 <= len <= left /\ len <= t_have X) by (rewrite EFL; destruct (Z.ltb_spec left (t_have X)); lia).
  (* [comment removed for export] *)
  assert (KTSB : forall (v15 v16 w9 : word) (mA : mem), mA = m' -> w9 = wz last ->
    evt usegs (slow_post_gen r F fc L (st_femit X flush) (bs_code (if negb (last =? 0) then finish_started else need_more)) inp rest0 lo me)
      (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -112)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) w9 (wz (dl_Aw L)) (wz (ds_block_start X + dl_Aw L)) (wz (ds_block_start X))
               (wz 1) (wz 0) v15 v16 y17 (wz len) (wz 1) y20 (wz (dl_As L + 5928)) (wz (if flush =? 4 then 1 else 0)) (wz ai0) (wz 32768) (wz (if flush =? 0 then 0 else 1)) (wz 65535) (wz 65534) y28 y29 y30 y31)
          F (wz Z_STO_TSBF) fc None mA (seg_rom usegs))).
  2:{ (* [comment removed for export] *)
      assert (K78 : forall (v9 v10 v14 : word) (mA : mem), mA = m' -> last = 0 ->
        evt usegs (slow_post_gen r F fc L (st_femit X flush) (bs_code (if negb (last =? 0) then finish_started else need_more)) inp rest0 lo me)
          (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -112)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) v9 v10 (wz (t_have X)) (wz (ds_block_start X))
                   (wz left) v14 y15 y16 y17 (wz len) (wz 1) y20 (wz (dl_As L + 5928)) (wz (if flush =? 4 then 1 else 0)) (wz ai0) (wz 32768) (wz (if flush =? 0 then 0 else 1)) (wz 65535) (wz 65534) y28 y29 y30 y31)
              F (wz 0x18d6c) fc None mA (seg_rom usegs))).
      { intros v9 v10 v14 mA -> L0. zstep. zs. zstep. zstep. zstep. zstep. guard_b2z. br_false.
        apply (KTSB _ _ _ _ eq_refl). rewrite L0. reflexivity. }
      zstep. zs. zstep. br_cases K2.
      - (* [comment removed for export] *)
        replace (flush =? Z_FINISH) with false in ELAST by (symmetry; apply Z.eqb_neq; unfold Z_FINISH; lia). cbn [andb] in ELAST.
        apply (K78 _ _ _ _ eq_refl ELAST).
      - replace (flush =? Z_FINISH) with true in ELAST by (symmetry; apply Z.eqb_eq; unfold Z_FINISH; lia). cbn [andb] in ELAST.
        zs. gF. zstep. al8 (dl_S L). gF. zs. zstep. br_cases K3.
        + (* [comment removed for export] *)
          replace (cs_avail_in (ds_strm X) =? 0) with true in ELAST by (symmetry; apply Z.eqb_eq; lia). cbn [andb] in ELAST.
          zs. zs. zstep. zstep. zs. zstep. zstep. zstep. zstep. guard_b2z. br_true.
          apply (KTSB _ _ _ _ eq_refl). rewrite ELAST. f_equal.
          rewrite EFL. destruct (Z.ltb_spec (t_have X) left); destruct (Z.ltb_spec left (t_have X)); try lia.
          * replace (t_have X =? left) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
          * rewrite Z.eqb_refl. reflexivity.
          * replace (t_have X =? left) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
        + replace (cs_avail_in (ds_strm X) =? 0) with false in ELAST by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ELAST.
          apply (K78 _ _ _ _ eq_refl ELAST). }
  intros v15 v16 w9 mA -> ->. unfold Z_STO_TSBF.
  (* [comment removed for export] *)
  destruct (FOK FC) as (BI0 & RP1 & FPOK). clear FOK.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -112)) = bv_unsigned (r_sp r) + -112) by (apply unsigned_lit; lia).
  unfold dout in DOUT. pose proof (outv_length rest0 (ds_strm X) (unbox _ RM)) as OL.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. rewrite (xor_guard_idx (ds_block_start X + dl_Aw L) (dl_Aw L) (ds_block_start X)) by lia. zstep. br_false.
  zstep. zstep. zstep.
  replace (wz (ds_block_start X + dl_Aw L)) with (wz (dl_Aw L + ds_block_start X)) by (f_equal; lia).
  clear GA.
  zstep. call (HTSB L X (Some (ds_block_start X)) len last lo).
  1:{ exact ST0. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. eapply dlay_below_lower; [exact BEL| lia]. }
  1:{ exact BI0. } 1:{ exact RP1. } 1:{ intros _ C; discriminate C. } 1:{ cbn [fb_buf_ok]. lia. } 1:{ lia. } 1:{ exact RL. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem m1. rewrite ESP in PC. rename PC into STK1. clear ST0. try clear GB. try clear GC. try clear GD. try clear Glt. try clear Gdt. try clear Gbt. try clear Gblc. try clear Gheap. try clear Gdep. try clear Gwin. try clear Gprev. try clear Ghead. try clear Gpend. try clear LENS. try clear LAY0.
  assert (HX1 : exists X1, X1 = tr_stored_block X (Some (ds_block_start X)) len last) by (eexists; reflexivity). destruct HX1 as [X1 EX1].
  pose proof (sb_keep X (Some (ds_block_start X)) len last) as KK. cbv zeta in KK. rewrite <- EX1 in KK, RP1, FPOK, POST. destruct KK as (K1s & K1w & K1ws & K1hs & K1lbs & K1bs & K1str).
  open_DST POST. open_A GA. rewrite K1bs in GA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m1) as MUf. pose proof (wmono_refl usegs m1) as WMf.
  (* [comment removed for export] *)
  zs. zstep. zstep. zstep. rewrite ?(Z.add_0_l 9223372036854775808). rewrite (slti0_false len) by lia. rewrite (slt_lxor (ds_block_start X + len) (ds_block_start X)) by lia.
  replace (ds_block_start X + len <? ds_block_start X) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. gF.
  zs. zs. name_mem mB.
  assert (HX2 : exists X2, X2 = set_block_start X1 (ds_block_start X1 + len)) by (eexists; reflexivity). destruct HX2 as [X2 EX2].
  rewrite <- EX2 in FPOK.
  assert (K2s : ds_strm X2 = ds_strm X1) by (rewrite EX2; reflexivity).
  assert (K2lbs : ds_lit_bufsize X2 = ds_lit_bufsize X1) by (rewrite EX2; reflexivity).
  tr_groups MUf WMf.
  assert (ST2 : DST mB L X2).
  { rewrite EX2, K1bs.
    constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY]. }
  clear GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf WMf LAY0 LENS GA.
  assert (ES : ds_strm X2 = ds_strm X) by (rewrite K2s; exact K1s).
  assert (EF : st_femit X flush = flush_pending X2).
  { unfold st_femit. cbv zeta. rewrite <- Elen0, <- Elast0, <- EX1, <- EX2. reflexivity. }
  unfold Q in RMF. rewrite st_final_eq, FC, fst_pr in RMF. rewrite EF in RMF |- *.
  assert (DR2 : DREP mB L X2) by (split; [exists zp1, zp2, zp3, zresv; rewrite ES; exact ZS| exact ST2]).
  assert (OUT2 : dout mB L rest0 (ds_strm X2)) by (unfold dout; rewrite ES; exact DOUT).
  assert (FP2 : fp_ok X2) by (apply fp_ok_of_so; [rewrite K2lbs, K1lbs; exact LBS| exact FPOK]).
  clear ZS ST2 DOUT.
  (* [comment removed for export] *)
  zstep. call (flush_pending_spec HTFB L X2 rest0 (zlength inp) lo).
  1:{ exact DR2. } 1:{ exact OUT2. } 1:{ eassumption. } 1:{ rewrite ESP. exact STK1. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. eapply dlay_below_lower; [exact BEL| lia]. }
  1:{ exact IO. } 1:{ exact FP2. } 1:{ rewrite K2lbs, K1lbs, LBS. reflexivity. } 1:{ rewrite ES. exact RAO. } 1:{ exact (unbox _ RMF). } 1:{ reflexivity. }
  name_mem m2. rewrite ESP in PC. rename PC into STK2.
  (* [comment removed for export] *)
  assert (ECODE : bs_code (if negb (last =? 0) then finish_started else need_more) = last * 2).
  { destruct (Z.eq_dec last 0) as [E|E]; [rewrite E; reflexivity|]. replace last with 1 by lia. reflexivity. }
  rewrite ECODE.
  zstep. br_cases KL; rewrite ?unsigned_lit in KL by lia.
  - replace (last * 2) with 0 by lia. zstep. zstep.
    eapply (sto_epi9 1).
    split; [exact PC0|]. split; [exact POST|]. split; [exact RMF|]. split; [exact FR|]. split; [exact STK2|].
    split; [exact MU|]. split; [exact WM| exact MI].
  - replace (last * 2) with 2 by lia. zstep.
    eapply (sto_epi9bu 1).
    split; [exact PC0|]. split; [exact POST|]. split; [exact RMF|]. split; [exact FR|]. split; [exact STK2|].
    split; [exact MU|]. split; [exact WM| exact MI].
Qed.

Lemma sto_final : KFIN L flush ai0 rest0 lo r F fc me Q X.
Proof using RMF FOK RAO RAI LBS PBS WS HV left HTFB HTSB HFL CTX.
  unfold KFIN, TK10. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_FINAL, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (lo_S _ LAY) as BKS. unfold blk_ok in BKS.
  pose proof (vi_str _ HV) as Vstr. pose proof (vi_bs _ HV) as Vbs. pose proof (vi_bv _ HV) as Vbv. pose proof (vi_ai _ HV) as Vai. rewrite WS in Vstr.
  pose proof (sb_hdr_eq X Vbv) as [EH RH].
  destruct (t_have_eq X Vbv ltac:(lia)) as (ETH & RTH & _). rewrite PBS in ETH.
  replace (65536 - (ds_bi_valid X + 42) / 2 ^ 3 <? 65536) with true in ETH by (symmetry; apply Z.ltb_lt; lia).
  assert (ETH' : t_have X = ds_pending_buf_size X - (ds_bi_valid X + 42) / 2 ^ 3) by (rewrite PBS; exact ETH).
  pose proof (t_mb_eq X ltac:(lia)) as EMB. rewrite WS in EMB. replace (t_have X <=? 32768) with false in EMB by (symmetry; apply Z.leb_gt; lia).
  open_DST ST. open_A GA. open_D GD. open_zs ZS. unfold sto_W, slow_W in MU.
  (* [comment removed for export] *)
  zs. zs. zs. zs. rewrite hdr_srlw by lia. rewrite Z.shiftr_div_pow2 by lia. zstep.
  change (2 ^ 3) with 8 in *.
  replace (wz (ds_pending_buf_size X - (ds_bi_valid X + 42) / 8)) with (wz (t_have X)) by (rewrite ETH'; reflexivity).
  zstep. zstep. zstep. br_cases K1; [| exfalso; clear - K1 PBS RH RTH ETH; lia].
  (* [comment removed for export] *)
  zs. zstep. zstep. zstep.
  rewrite (slt0_lxor (ds_block_start X)) by lia. rewrite (lss_guard (ds_block_start X) (ds_strstart X)) by lia.
  zstep. rewrite bv_eqb_refl. change (negb true) with false. cbv iota. fold left.
  zs. zs. zstep. br_cases K2; [| exfalso; clear - K2 ETH RH WS RTH PBS; lia].
  zs. rewrite (Z.add_0_r left).
  assert (KNO : forall (v9 v11 v12 v13 v14 v15 v16 : word), fin_cond X flush = false ->
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -112)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) v9 (wz 0) v11 v12 v13 v14 v15 v16 y17
                     y18 (wz 1) y20 (wz (dl_As L + 5928)) (wz (if flush =? 4 then 1 else 0)) (wz ai0) (wz 32768) (wz (if flush =? 0 then 0 else 1)) (wz 65535) (wz 65534) y28 y29 y30 y31) F (wz Z_STO_EPI) fc None m' (seg_rom usegs))).
  { intros v9 v11 v12 v13 v14 v15 v16 NFC. unfold Q. rewrite st_final_eq, NFC, fst_pr, snd_pr. apply (sto_epi9 1). exact INV. }
  zstep. br_cases K3.
  { (* [comment removed for export] *)
    eapply fin_emitf; [exact INV|].
    unfold fin_cond. cbv zeta. rewrite EMB. subst left. rewrite wrap32_mod, Z.mod_small by lia.
    replace (32768 <=? ds_strstart X - ds_block_start X) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  (* [comment removed for export] *)
  assert (EFC : fin_cond X flush = ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) && (cs_avail_in (ds_strm X) =? 0))).
  { unfold fin_cond. cbv zeta. rewrite EMB. subst left. rewrite wrap32_mod, Z.mod_small by lia.
    replace (32768 <=? ds_strstart X - ds_block_start X) with false by (symmetry; apply Z.leb_gt; lia). cbn [orb].
    replace (ds_strstart X - ds_block_start X <=? t_have X) with true by (symmetry; apply Z.leb_le; lia). rewrite Bool.andb_true_r. reflexivity. }
  zstep. zs. zstep. br_cases K4.
  { (* [comment removed for export] *) apply KNO. rewrite EFC. replace (flush =? Z_NO_FLUSH) with true by (symmetry; apply Z.eqb_eq; unfold Z_NO_FLUSH; lia).
    rewrite Bool.andb_false_r. reflexivity. }
  zs. zstep. zstep. rewrite ?(Z.add_0_r left).
  rewrite (cond2_mach14 flush left) by lia.
  replace (flush =? Z_NO_FLUSH) with false in EFC by (symmetry; apply Z.eqb_neq; unfold Z_NO_FLUSH; lia). unfold Z_FINISH in EFC.
  destruct (negb (left =? 0) || (flush =? 4)) eqn:EB; cbn [negb andb] in EFC.
  2:{ zstep. br_cases K5; [| exfalso; clear - K5; cbn in K5; lia]. apply KNO. exact EFC. }
  zstep. br_cases K5; [exfalso; clear - K5; cbn in K5; lia|].
  zs. gF. zstep. al8 (dl_S L). gF. zs. zstep. zstep. br_cases K6.
  { (* [comment removed for export] *) apply KNO. rewrite EFC. apply Z.eqb_neq. lia. }
  (* [comment removed for export] *)
  zs. zs. rewrite ?(Z.add_0_r left), ?(Z.add_0_r (t_have X)). zstep. br_cases K7; [exfalso; clear - K7 K3 K2 RTH ETH PBS RH WS; lia|].
  eapply fin_emitf; [exact INV|]. rewrite EFC. apply Z.eqb_eq. lia.
Qed.
End FIN.
