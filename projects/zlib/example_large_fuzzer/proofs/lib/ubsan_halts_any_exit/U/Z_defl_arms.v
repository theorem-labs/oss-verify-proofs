(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_defl_kit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Section ARMS.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : defl_ctx L inp rest0 lo r me.
Lemma defl_buferr : forall (Q : machine_state -> Prop) (X : deflate_state) (pc : Z)
    (y1 y5 y6 y7 y8 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word) (m : mem),
  pc = 0x17364 \/ pc = 0x173a4 \/ pc = 0x17764 ->
  DINV L rest0 lo r me X m ->
  DKE L rest0 lo r F fc me Q (wz (-5)) (fst (err_return X Z_BUF_ERROR)) ->
  evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 (wz (dl_S L)) (wz (dl_S L)) y11 y12 y13 y14 y15 y16 y17
                       y18 (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz pc) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPC (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) HK.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK in LOsp. apply box in SP16.
  assert (RLP : relro_clean m) by (apply (defl_relro L inp rest0 lo r me CTX); exact MU).
  destruct (errmsg_cells _ RLP) as [GOTE TABE]. unfold Z_GOT_ERRMSG in GOTE. unfold Z_ERRMSG, Z_ERRMSG_PTRS in TABE, GOTE. cbn [map] in TABE.
  destruct DR as [ZS ST]. open_zs ZS. lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold defl_frame in FR. unfold defl_W in MU. unfold DKE, Z_DEFL_EPI in HK.
  pose proof (munch_refl [(dl_S L, dl_S L + 112)] m) as MUg. pose proof (wmono_refl usegs m) as WMg.
  assert (FIN : forall mE, munch [(dl_S L, dl_S L + 112)] m mE -> wmono usegs m mE -> mem_inv usegs mE ->
            munch (defl_W L rest0 lo r) me mE -> wmono usegs me mE ->
            rw_cells usegs mE (bv_unsigned (r_sp r) + -64) (defl_frame j0 r) -> stk usegs mE lo (bv_unsigned (r_sp r) + -64) ->
            dzs mE L (cset_msg (ds_strm X) (MSG_ERR Z_BUF_ERROR)) ->
            DINV L rest0 lo r me (fst (err_return X Z_BUF_ERROR)) mE).
  { intros mE MUg' WMg' MI' MU' WM' FR' STK' ZS'.
    split; [split|].
    - unfold err_return. cbn [fst]. dsred. exact ZS'.
    - apply DST_set_strm; [intros HB; exact HB|].
      apply (DST_agree m mE L X ST). eapply ag_blocks_munch; [exact (st_lay _ _ _ _ ST)| exact MUg'| exact WMg'| | | | |]; cbn [disjoint_from]; slia.
    - split; [unfold err_return; cbn [fst]; dsred; apply (dout_munch _ m mE L rest0 _ DOUT ROOM MUg' WMg'); cbn [disjoint_from]; slia|].
      split; [unfold err_return; cbn [fst]; dsred; exact ROOM|].
      split; [eexists; exact FR'|]. split; [exact STK'|]. split; [exact MU'|]. split; [exact WM'| exact MI']. }
  assert (TAIL : forall (z11 z12 : word),
    evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -64)) (r_gp r) (r_tp r) y5 y6 y7 y8 (wz (dl_S L)) (wz 0x2c2f8) z11 z12 y13 y14 y15 y16 y17
                     y18 (r_s3 r) (r_s4 r) (r_s5 r) (r_s6 r) (r_s7 r) (r_s8 r) (r_s9 r) (r_s10 r) (r_s11 r) y28 y29 y30 y31) F (wz 0x1736c) fc None m (seg_rom usegs))).
  { intros z11 z12. zstep. gT. zs. zs. name_mem mE. zstep. zstep.
    eapply HK. apply FIN; [exact MUg| exact WMg| eassumption| exact MU| exact WM| exact FR| exact STK|].
    unfold Z_BUF_ERROR, MSG_ERR. cbn [Z.ltb Z.compare Pos.compare Pos.compare_cont orb Z.sub Z.opp Z.add Z.pos_sub Pos.pred_double].
    do 4 eexists. unfold zs_call_cells, zs_priv_cells. cbn [app]. dsred. close_cells ZS. }
  destruct HPC as [->|[->| ->]].
  - zstep. zs. apply TAIL.
  - zstep. zs. zstep. apply TAIL.
  - zstep. zs. zstep. apply TAIL.
Qed.
End ARMS.
