(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_ukit Zg_defl_iface Zg_sto_kit Zg_sto_head Zg_sto_emit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_RDO : Z := 0x18974.

(* [comment removed for export] *)
Ltac join_x20 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode ?O None (TNode (TNode ?P ?o4 (TNode (TNode TEmpty (Some _) TEmpty) ?o12 ?D)) ?o2 ?E)) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut usegs (fun ms' => ms' = MS (TNode O None (TNode (TNode P o4 (TNode (TNode TEmpty (Some v) TEmpty) o12 D)) o2 E)) F (wz pcj) fc None m rom))
  end.

Section COPY.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.

(* [comment removed for export] *)
Definition KRDO (Q : machine_state -> Prop) (last : Z) (X5 : deflate_state) (n2 : Z) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush rest0 lo r me X5 m' ->
    evt usegs Q (MS (stoR L flush ai0 last r y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (wz n2) y20 y28 y29 y30 y31)
                    F (wz Z_STO_RDO) fc None m' (seg_rom usegs)).

Variables (Q : machine_state -> Prop) (X X4 : deflate_state).
Let left := ds_strstart X - ds_block_start X.
Let len := sb_len X.
Let n1 := lc_len left len.
Hypothesis RBS : 0 <= ds_block_start X <= ds_strstart X.
Hypothesis RSTR : ds_strstart X <= 65536.
Hypothesis RLEN : 0 <= sb_len X <= 65535.
Hypothesis E4bs : ds_block_start X4 = ds_block_start X.
Hypothesis E4str : ds_strstart X4 = ds_strstart X.
Hypothesis RAO4 : 0 <= cs_avail_out (ds_strm X4) < 2^31.
Hypothesis RN1 : left <> 0 -> n1 <= cs_avail_out (ds_strm X4).
Hypothesis RM5 : Box (length (cs_out_rev (ds_strm (fst (st_copy X4 left len)))) <= length rest0)%nat.
Hypothesis KR : KRDO Q (sb_lastv X flush) (fst (st_copy X4 left len)) (snd (st_copy X4 left len)).

Lemma sto_copy : KCOPY L flush ai0 rest0 lo r F fc me Q X X4.
Proof using KR RM5 RN1 RAO4 E4bs RLEN RSTR RBS n1 len left CTX inp.
  unfold KCOPY. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & FR & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_COPY, stoR.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'.
  pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (lo_S _ LAY) as BKS. unfold blk_ok in BKS.
  unfold KRDO in KR.
  zstep. br_cases K.
  { (* [comment removed for export] *)
    assert (EL0 : left = 0) by (subst left; lia).
    unfold st_copy in KR, RM5. replace (negb (left =? 0)) with false in KR, RM5 by (rewrite EL0; reflexivity). cbn [fst snd] in KR, RM5.
    eapply KR. exact INV. }
  assert (NL0 : left <> 0) by (subst left; lia).
  unfold st_copy in KR, RM5. replace (negb (left =? 0)) with true in KR, RM5 by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; exact NL0). cbn [fst snd] in KR, RM5.
  pose proof (RN1 NL0) as RN.
  assert (RN1' : 0 <= n1 <= len /\ n1 <= left) by (subst n1 left len; unfold lc_len; destruct (Z.ltb_spec (sb_len X) (ds_strstart X - ds_block_start X)); lia).
  (* [comment removed for export] *)
  zstep. zstep. join_x20 (wz n1) 0x188c8.
  { if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - replace (wz n1) with (wz (sb_len X))
        by (f_equal; subst n1 left len; unfold lc_len; destruct (Z.ltb_spec (sb_len X) (ds_strstart X - ds_block_start X)); lia).
      apply evt_done. reflexivity.
    - zstep. replace (wz n1) with (wz (ds_strstart X - ds_block_start X))
        by (f_equal; subst n1 left len; unfold lc_len; destruct (Z.ltb_spec (sb_len X) (ds_strstart X - ds_block_start X)); lia).
      apply evt_done. reflexivity. }
  intros ms' ->.
  open_DST ST. open_A GA. open_zs ZS. open_win Gwin.
  unfold dout in DOUT. pose proof (outv_length rest0 (ds_strm X4) (unbox _ RM)) as OL.
  rewrite E4bs in GA.
  zs. gF. zstep. al8 (dl_S L). gF.
  zstep. zstep. zstep. zstep. zstep.
  zstep. guard_b2z. br_false.
  zstep. zstep. zstep. zstep. zstep. rewrite (xor_guard_idx (ds_block_start X + dl_Aw L) (dl_Aw L) (ds_block_start X)) by lia. br_false.
  zstep. rewrite ?Z.mod_small by lia. zstep.
  replace (wz (ds_block_start X + dl_Aw L)) with (wz (dl_Aw L + ds_block_start X)) by (f_equal; lia).
  (* [comment removed for export] *)
  remember (length (cs_out_rev (ds_strm X4))) as k eqn:Ek.
  assert (KL : (k + Z.to_nat n1 <= length rest0)%nat).
  { pose proof (unbox _ RM5) as R5. unfold st_lcopy in R5. dsred in R5. rewrite cs_emit_out_len, arr_slice_length', <- Ek in R5. lia. }
  pose proof (u8arr_sub_bytes _ (dl_Aw L) _ (Z.to_nat (ds_block_start X)) (Z.to_nat n1) Gwin ltac:(rewrite av8_length; lia)) as SRC.
  rewrite av8_slice in SRC by lia. rewrite Z2Nat.id in SRC by lia.
  assert (LSRC : length (map (Z_to_bv 8) (arr_slice (ds_window X4) (ds_block_start X) n1)) = Z.to_nat n1) by (rewrite length_map; apply arr_slice_length').
  destruct (u8arr_split3 _ (dl_NO L) _ k (Z.to_nat n1) DOUT ltac:(rewrite OL; lia)) as (O1 & O2 & O3). clear DOUT.
  assert (LO1 : length (firstn k (outv rest0 (ds_strm X4))) = k) by (rewrite length_firstn, OL; lia).
  assert (LO3 : length (skipn (k + Z.to_nat n1) (outv rest0 (ds_strm X4))) = (length rest0 - (k + Z.to_nat n1))%nat) by (rewrite length_skipn, OL; lia).
  unfold sto_W, slow_W in MU.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (munch_refl [(dl_NO L, dl_NO L + Z.of_nat (length rest0)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212)] mc) as MUf;
    pose proof (wmono_refl usegs mc) as WMf end.
  zstep. call (memcpy_Z (dl_NO L + Z.of_nat k) (dl_Aw L + ds_block_start X) n1).
  1:{ exact SRC. } 1:{ exact LSRC. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  pose proof (u8arr_join3k _ (dl_NO L) _ _ _ k (Z.to_nat n1) LO1 O1 PC O3) as OUT.
  fold (zb8 (arr_slice (ds_window X4) (ds_block_start X) n1)) in OUT.
  rewrite <- (arr_slice_length' (ds_window X4) (ds_block_start X) n1) in OUT. rewrite Ek in OUT.
  rewrite <- outv_emit in OUT by (rewrite <- Ek, arr_slice_length'; exact KL).
  assert (OL' : length (outv rest0 (cs_emit (ds_strm X4) (arr_slice (ds_window X4) (ds_block_start X) n1))) = length rest0).
  { apply outv_length. rewrite cs_emit_out_len, arr_slice_length', <- Ek. lia. }
  clear O1 O3 PC POST SRC LSRC LO1 LO3.
  (* [comment removed for export] *)
  zs. gF. zstep. al8 (dl_S L). gF.
  zstep. zstep. gF. zstep. zstep. zstep. gX.
  zs. zs. zs. zstep. zs. zs. zs. zstep.
  rewrite (slti0_false n1) by lia. rewrite (slt_lxor (ds_block_start X + n1) (ds_block_start X)) by lia.
  replace (ds_block_start X + n1 <? ds_block_start X) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zs. zs. zs. gF. zs. zs.
  tr_groups MUf WMf. eapply KR.
  unfold st_lcopy. rewrite E4bs.
  split; [split|].
  - eexists _, _, _, _. unfold zs_call_cells, zs_priv_cells. cbn [app]. unfold cs_emit. dsred.
    rewrite ?rev_append_rev, ?length_app, ?length_rev, ?arr_slice_length', <- ?Ek. close_cells ZS.
  - constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | unfold dwin; dsred; exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY].
  - split; [unfold dout; dsred; exact OUT|].
    split; [constructor; dsred; rewrite cs_emit_out_len, arr_slice_length', <- Ek; exact KL|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.
End COPY.
