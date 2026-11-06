(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_KitH ECH_LibState
     ECH_B64 ECH_C1_stmt ECH_C8_stmt ECH_C8_blockA ECH_C8_block.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog StrFun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition DF_RA : Z := 0x1daee0.
Definition DF_EXIT : Z := 0x1daef0.
Definition df_frame (j : list byte) (s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Section CHUNK.
  Context {HCEIL : HeapCeil}.
  Lemma ctx_chunk_of_enc : forall m a x raw line,
    rw_cells rsegs m a [C4 (wz x); CB 80 raw; C4 (wz line); C4 (wz 0)] -> rw_cells rsegs m a (ctx_chunk x raw line).
  Proof.
    intros m a x raw line H. unfold ctx_chunk.
    change [C4 (wz x); CB 80 raw; C4 (wz line); C4 (wz 0)] with ([C4 (wz x); CB 80 raw; C4 (wz line)] ++ [C4 (wz 0)]) in H.
    change [C4 (wz x); CB 80 raw; C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]] with ([C4 (wz x); CB 80 raw; C4 (wz line)] ++ [CB 4 [b8 0; b8 0; b8 0; b8 0]]).
    apply rw_cells_app in H. destruct H as [H1 H2]. apply rw_cells_app. split; [exact H1|].
    eapply rw_cells_recut; [exact H2| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
  Qed.
  Lemma enc_of_ctx_chunk : forall m a x raw line,
    rw_cells rsegs m a (ctx_chunk x raw line) -> rw_cells rsegs m a [C4 (wz x); CB 80 raw; C4 (wz line); C4 (wz 0)].
  Proof.
    intros m a x raw line H. unfold ctx_chunk in H.
    change [C4 (wz x); CB 80 raw; C4 (wz line); C4 (wz 0)] with ([C4 (wz x); CB 80 raw; C4 (wz line)] ++ [C4 (wz 0)]).
    change [C4 (wz x); CB 80 raw; C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]] with ([C4 (wz x); CB 80 raw; C4 (wz line)] ++ [CB 4 [b8 0; b8 0; b8 0; b8 0]]) in H.
    apply rw_cells_app in H. destruct H as [H1 H2]. apply rw_cells_app. split; [exact H1|].
    eapply rw_cells_recut; [exact H2| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
  Qed.
  (* [comment removed for export] *)
  Lemma decode_final_rv_bad : forall d, du_inv d -> (0 < length d)%nat -> Nat.modulo (length d) 4 <> 0%nat -> decode_final_rv d = -1.
  Proof.
    intros d [F _] L M. unfold decode_final_rv, decodeblock_ret, decodeblock.
    replace (length d =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia). cbn [orb Z.ltb Z.compare].
    rewrite (trim_block_saved d) by (eapply Forall_impl; [| exact F]; intros c Hc; apply b64_saved_lt64; exact Hc).
    replace (Z.of_nat (length d) mod 4 =? 0) with false; [reflexivity|].
    symmetry. apply Z.eqb_neq. rewrite <- (Nat2Z.inj_mod _ 4). change (Z.of_nat 4) with 4. lia.
  Qed.
End CHUNK.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].

  (* [comment removed for export] *)
  Lemma df_empty :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a outlp ov lo line : Z) (raw : list byte),
      rw_cells rsegs m a (ctx_chunk 0 raw line) -> 0 < a -> a + 92 <= lo ->
      rw_cells rsegs m outlp [C4 (wz ov)] -> (outlp + 4 <= lo \/ bv_unsigned sp <= outlp) -> (outlp + 4 <= a \/ a + 92 <= outlp) ->
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (fun ms' => exists x12 x13 m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp); (outlp, outlp + 4)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp) /\ rw_cells rsegs m1 a (ctx_chunk 0 raw line) /\ rw_cells rsegs m1 outlp [C4 (wz 0)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 (Z_to_bv 64 outlp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeFinal) fc None m (seg_rom rsegs)).
  Proof.
    intros until raw. intros CTX POS BL OL OSEP OA ST LO MI RAE. unfold P_EVP_DecodeFinal.
    pose proof (rw_cells_bound _ _ _ _ CTX) as HB. cbn [cells_size csize Nat.add length] in HB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (outlp, outlp + 4)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold ctx_chunk, wz in CTX, OL |- *.
    carve_frame 48%nat ST.
    do 7 step. st1. st1. step. step. try if_lit.
    step. do 5 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma df_call :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a outlp ov lo nn line : Z) (raw : list byte),
      rw_cells rsegs m a (ctx_chunk nn raw line) -> 0 < a -> a + 92 <= lo -> 0 < nn < 2^31 ->
      rw_cells rsegs m outlp [C4 (wz ov)] -> (outlp + 4 <= lo \/ bv_unsigned sp <= outlp) -> (outlp + 4 <= a \/ a + 92 <= outlp) ->
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 DF_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 outlp) (Z_to_bv 64 a) (Z_to_bv 64 0) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 nn) (Z_to_bv 64 (-1)) a5 a6 a7
                       (Z_to_bv 64 a) (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_evp_decodeblock_int) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp); (outlp, outlp + 4)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -48) /\ rw_cells rsegs m1 (bv_unsigned sp + -48) (df_frame j s3 s2 s1 s0 ra)
          /\ rw_cells rsegs m1 a (ctx_chunk nn raw line) /\ rw_cells rsegs m1 outlp [C4 (wz 0)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 0) (Z_to_bv 64 outlp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeFinal) fc None m (seg_rom rsegs)).
  Proof.
    intros until raw. intros CTX POS BL NN OL OSEP OA ST LO MI RAE. unfold P_EVP_DecodeFinal, P_evp_decodeblock_int, DF_RA.
    pose proof (rw_cells_bound _ _ _ _ CTX) as HB. cbn [cells_size csize Nat.add length] in HB.
    pose proof (rw_cells_bound _ _ _ _ OL) as OB. cbn [cells_size csize Nat.add length] in OB.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (outlp, outlp + 4)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold ctx_chunk, wz in CTX, OL |- *.
    carve_frame 48%nat ST.
    do 7 step. st1. st1. change (Z_to_bv 64 nn) with (wz nn). rewrite sx32_wz by lia. unfold wz. step. step. fbr.
    do 6 step. finish.
    all: try exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma df_ret :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 q1 q2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (j : list byte),
      rw_cells rsegs m (bv_unsigned sp + -48) (df_frame j s3 s2 s1 s0 ra) ->
      stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
      evt rsegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom rsegs)
          /\ stk rsegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 DF_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp q1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
                 q2 (Z_to_bv 64 (-1)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DF_RA)) fc None m (seg_rom rsegs)).
  Proof.
    intros until j. intros FR ST LO MI. unfold DF_RA.
    replace (ret_pc (Z_to_bv 64 0x1daee0)) with (Z_to_bv 64 0x1daee0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold df_frame in FR.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. try if_lit. step. do 5 st1. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. split; [reflexivity| exact ST].
  Qed.

  Lemma decfinal_spec : decfinal_stmt.
  Proof.
    unfold decfinal_stmt. intros until d. intros A0 A1 A2 EC TAB DC OL OSEP OA BL ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold DECFINAL_STACK, FR_EVP_DecodeFinal, DECBLOCK_STACK, FR_evp_decodeblock_int in LO. unfold ENCCTX_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct EC as (raw & line & L80 & RD & CELLS & LR & EIN & EBR & DI).
    pose proof EBR as (POS & _).
    pose proof (ctx_chunk_of_enc _ _ _ _ _ CELLS) as CTX.
    unfold c8_post.
    destruct (Nat.eq_dec (length d) 0) as [D0|DN].
    - (* [comment removed for export] *)
      assert (d = []) as -> by (destruct d; [reflexivity| cbn in D0; lia]). change (zlength []) with 0 in CTX.
      eapply evt_mono; [eapply df_empty; try eassumption; lia|].
      intros ms' (x12 & x13 & m1 & -> & MU1 & WM1 & MI1 & ST1 & CTX1 & OL1).
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m1. split; [reflexivity|].
      split; [unfold decode_final_rv; cbn; reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. intros z Hz. cbn in Hz |- *. lia. }
      split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      split. { exists raw, line. split; [exact L80|]. split; [exact RD|]. split; [apply enc_of_ctx_chunk; exact CTX1|].
               split; [exact LR|]. split; [exact EIN|]. split; [exact EBR| exact DI]. }
      split; [exact OL1| apply B64TAB_of_mem_inv; exact MI1].
    - (* [comment removed for export] *)
      assert (DM : Nat.modulo (length d) 4 <> 0%nat) by (destruct DC as [DC|DC]; [lia| exact DC]).
      pose proof DI as [DF D64].
      eapply evt_cut; [eapply df_call; try eassumption; unfold zlength; try lia|].
      intros ms1 (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & CTX1 & OL1).
      eapply evt_cut.
      { eapply (decblock_bad_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 a (zlength d) lo); rewrite ?unsigned_lit by lia; try eassumption.
        all: lazymatch goal with
             | |- Forall _ _ => unfold zlength; rewrite Nat2Z.id, RD; exact DF
             | |- bv_unsigned _ mod 2 = 0 => unfold DF_RA; rewrite unsigned_lit by lia; reflexivity
             | |- not (_ mod 4 = 0) => unfold zlength; rewrite <- (Nat2Z.inj_mod _ 4); change (Z.of_nat 4) with 4; lia
             | |- _ => unfold zlength; lia
             end. }
      intros ms2 PO. unfold db_post in PO.
      destruct PO as (y0 & y1 & y2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & CTX2).
      rewrite (unsigned_lit (bv_unsigned sp + -48)) in MU2, ST2 by lia.
      apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1) in MU2 as FR2; [| exact WM2| cbn; lia].
      apply (rw_cells_transport rsegs _ m1 m2 _ _ OL1) in MU2 as OL2; [| exact WM2| cbn; lia].
      eapply evt_mono; [eapply df_ret; [exact FR2| exact ST2| lia| exact MI2]|].
      intros ms3 (-> & ST3).
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m2. split; [reflexivity|].
      split; [rewrite (decode_final_rv_bad d DI ltac:(lia) DM); reflexivity|].
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; intros z Hz; cbn in Hz |- *; lia. }
      split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact ST3|].
      split. { exists raw, line. split; [exact L80|]. split; [exact RD|]. split; [apply enc_of_ctx_chunk; exact CTX2|].
               split; [exact LR|]. split; [exact EIN|]. split; [exact EBR| exact DI]. }
      split; [exact OL2| apply B64TAB_of_mem_inv; exact MI2].
  Qed.
End S.
