(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_defl_kit F_memcpy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate SendModel FillWinModel RefDeflFast1 RefDeflFastM DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section ARMS.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.

Lemma defl_lf : forall (Q : machine_state -> Prop) (X : deflate_state),
  DKE L rest0 lo r F fc me Q (wz 0) (set_last_flush X (-1)) -> DKL L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X HK. unfold DKL. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold deflR. unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m') as MUf. pose proof (wmono_refl psegs m') as WMf.
  zs. zs. zs. name_mem mA.
  tr_groups MUf WMf.
  eapply HK.
  split; [split|].
  - exact ZS.
  - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                 | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [apply (dout_munch _ m' mA L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|].
    split; [exact ROOM|]. split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma defl_buferr : forall (Q : machine_state -> Prop) (X : deflate_state) (pc : Z)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 y29 y30 y31 : word) (m : mem),
  pc = 0x16ebc \/ pc = 0x1722c \/ pc = 0x16ef4 ->
  DINV L rest0 lo r me X m ->
  DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return X Z_BUF_ERROR)) ->
  evt psegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 y9 (wz (dl_S L)) y11 y12 y13 y14 y15 y16 y17
                       y18 y19 y20 y21 y22 (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz pc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPC (DR & DOUT & ROOM & FR & STK & MU & WM & MI) HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  assert (RLP : relro_clean m) by (apply (defl_relro L inp rest0 lo r me CTX); exact MU).
  destruct (errmsg_cells _ RLP) as [GOTE TABE]. unfold Z_GOT_ERRMSG in GOTE. unfold Z_ERRMSG, Z_ERRMSG_PTRS in TABE, GOTE. cbn [map] in TABE.
  destruct DR as [ZS ST]. open_zs ZS. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold defl_frame in FR. unfold defl_W in MU.
  pose proof (munch_refl [(dl_S L, dl_S L + 112)] m) as MUg. pose proof (wmono_refl psegs m) as WMg.
  assert (FIN : forall mE, munch [(dl_S L, dl_S L + 112)] m mE -> wmono psegs m mE -> mem_inv psegs mE ->
            munch (defl_W L rest0 lo r) me mE -> wmono psegs me mE ->
            rw_cells psegs mE (bv_unsigned (r_sp r) + -64) (defl_frame r) -> stk psegs mE lo (bv_unsigned (r_sp r) + -64) ->
            dzs mE L (cset_msg (ds_strm X) (MSG_ERR Z_BUF_ERROR)) ->
            DINV L rest0 lo r me (fst (err_return X Z_BUF_ERROR)) mE).
  { intros mE MUg' WMg' MI' MU' WM' FR' STK' ZS'.
    split; [split|].
    - unfold err_return. cbn [fst]. dsred. exact ZS'.
    - apply DST_set_strm; [intros HB; exact HB|].
      apply (DST_agree m mE L X ST). eapply ag_blocks_munch; [exact (st_lay _ _ _ _ ST)| exact MUg'| exact WMg'| | | | |]; cbn [disjoint_from]; slia.
    - split; [unfold err_return; cbn [fst]; dsred; apply (dout_munch _ m mE L rest0 _ DOUT ROOM MUg' WMg'); cbn [disjoint_from]; slia|].
      split; [unfold err_return; cbn [fst]; dsred; exact ROOM|].
      split; [exact FR'|]. split; [exact STK'|]. split; [exact MU'|]. split; [exact WM'| exact MI']. }
  destruct HPC as [->|[->| ->]].
  - zs. zs. zs. zs. name_mem mE. zs. zs.
    eapply HK. apply FIN; [exact MUg| exact WMg| eassumption| exact MU| exact WM| exact FR| exact STK|].
    unfold Z_BUF_ERROR, MSG_ERR. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
    do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZS.
  - zs. zs. zs. zs. zs. name_mem mE. zs. zs.
    eapply HK. apply FIN; [exact MUg| exact WMg| eassumption| exact MU| exact WM| exact FR| exact STK|].
    unfold Z_BUF_ERROR, MSG_ERR. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
    do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZS.
  - zs. zs. zs. zs. zs. name_mem mE. zs. zs.
    eapply HK. apply FIN; [exact MUg| exact WMg| eassumption| exact MU| exact WM| exact FR| exact STK|].
    unfold Z_BUF_ERROR, MSG_ERR. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
    do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZS.
Qed.

End ARMS.
