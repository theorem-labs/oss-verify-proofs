(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C8 ECH_AKit ECH_AsKit ECH_AC8_small ECH_AC8_blockA ECH_AC8_block.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ADF_RA : Z := 0x422fc8.    (* [comment removed for export] *)
Definition ADF_J : Z := 0x422f88.     (* [comment removed for export] *)
Definition adf_frame (j : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section CHUNK.
  Context {HCEIL : HeapCeil}.
  Lemma ctx_chunk_of_enc : forall m a x raw line,
    rw_cells asegs m a [C4 (wz x); CB 80 raw; C4 (wz line); C4 (wz 0)] -> rw_cells asegs m a (ctx_chunk x raw line).
  Proof.
    intros m a x raw line H. unfold ctx_chunk.
    change [C4 (wz x); CB 80 raw; C4 (wz line); C4 (wz 0)] with ([C4 (wz x); CB 80 raw; C4 (wz line)] ++ [C4 (wz 0)]) in H.
    change [C4 (wz x); CB 80 raw; C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]] with ([C4 (wz x); CB 80 raw; C4 (wz line)] ++ [CB 4 [b8 0; b8 0; b8 0; b8 0]]).
    apply rw_cells_app in H. destruct H as [H1 H2]. apply rw_cells_app. split; [exact H1|].
    eapply rw_cells_recut; [exact H2| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
  Qed.
  Lemma enc_of_ctx_chunk : forall m a x raw line,
    rw_cells asegs m a (ctx_chunk x raw line) -> rw_cells asegs m a [C4 (wz x); CB 80 raw; C4 (wz line); C4 (wz 0)].
  Proof.
    intros m a x raw line H. unfold ctx_chunk in H.
    change [C4 (wz x); CB 80 raw; C4 (wz line); C4 (wz 0)] with ([C4 (wz x); CB 80 raw; C4 (wz line)] ++ [C4 (wz 0)]).
    change [C4 (wz x); CB 80 raw; C4 (wz line); CB 4 [b8 0; b8 0; b8 0; b8 0]] with ([C4 (wz x); CB 80 raw; C4 (wz line)] ++ [CB 4 [b8 0; b8 0; b8 0; b8 0]]) in H.
    apply rw_cells_app in H. destruct H as [H1 H2]. apply rw_cells_app. split; [exact H1|].
    eapply rw_cells_recut; [exact H2| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
  Qed.
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
  Lemma adf_p1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a outlp lo : Z),
      0 <= a < 2^64 -> 0 < outlp -> outlp mod 4 = 0 -> accessible m outlp 4 -> (aapp outlp 4 \/ bv_unsigned sp <= outlp) -> aceil <= lo -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j (x10 x12 : word),
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 outlp) x10 a1 x12 a3 a4 a5 a6 a7
                       (Z_to_bv 64 a) s3 (Z_to_bv 64 (Z.shiftr outlp 3 + 2147450880)) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ADF_J) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -64) /\ rw_cells asegs m1 (bv_unsigned sp + -64) (adf_frame j s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 (Z_to_bv 64 outlp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeFinal) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros AR OP OAL ACC0 OSH CEIL AC ST LO MI. unfold P_EVP_DecodeFinal, ADF_J.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ACONST_shbase _ AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m outlp 4)) in ACC'.
    carve_frame 64%nat ST.
    do 9 step.
    assert (NSH : outlp + 4 <= ALOWSH_LO \/ AHI_LO <= outlp).
    { destruct OSH as [OSH|OSH]; [exact (aapp_not_shadowland _ _ OSH)| right; unfold AHI_LO; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx outlp 4) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|];
        apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_nil]) end.
    pose proof ACC as (OR0 & OR1 & _). unfold AAPP_HI in OR1.
    step. ub_dead.
    step. step. step. ubal_by OAL. step. if_lit.
    step. step. step.
    zstep. try replace (Z.land outlp 18446744073709551615) with outlp by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    zstep. ck4_load ACC outlp v V1 V2 Ha.
    step. destruct (Z.eq_dec v 0) as [Ev|Nv].
    - if_false_by (ck1_bnez_false v Ev). finish. unfold adf_frame. exact FR.
    - if_true_by (ck1_bnez_true v V1 Nv). destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|].
      step. step. step. if_true_by (ck4_blt_true outlp v Ha V1 VV). finish. unfold adf_frame. exact FR.
  Qed.
End S.

Section S2.
  Context {HCEIL : HeapCeil}.
  Local Ltac tbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [| exfalso; lia].
  Local Ltac fbr := let K := fresh "K" in if_cases K; zify_cond K; try rewrite !signed_lit in * by lia; [exfalso; lia|].

  (* [comment removed for export] *)
  Lemma adf_empty :
    forall (ra sp gp tp t0 t1 t2 s0 s1 x10 a1 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a outlp ov lo line : Z) (raw j : list byte),
      rw_cells asegs m a (ctx_chunk 0 raw line) -> 0 < a -> a mod 16 = 0 -> a + 92 <= aceil -> aceil <= lo -> accessible m a 92 -> aapp a 92 ->
      rw_cells asegs m outlp [C4 (wz ov)] -> 0 < outlp -> outlp + 4 <= AAPP_HI -> (outlp + 4 <= lo \/ bv_unsigned sp <= outlp) -> (outlp + 4 <= a \/ a + 92 <= outlp) ->
      (outlp + 4 <= ALOWSH_LO \/ AHI_LO <= outlp) ->
      rw_cells asegs m (bv_unsigned sp + -64) (adf_frame j s5 s4 s3 s2 s1 s0 ra) ->
      stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (x12' x13' : word) m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 x12' x13' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -64, bv_unsigned sp); (outlp, outlp + 4)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp) /\ rw_cells asegs m1 a (ctx_chunk 0 raw line) /\ rw_cells asegs m1 outlp [C4 (wz 0)])
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 outlp) x10 a1 x12 a3 a4 a5 a6 a7
                 (Z_to_bv 64 a) s3 (Z_to_bv 64 (Z.shiftr outlp 3 + 2147450880)) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADF_J) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros CTX POS AL BL CEIL ACC0 AP OL OP OH OSEP OA NSH FR ST LO MI. unfold ADF_J.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold AAPP_HI in OH. pose proof (aapp_not_shadowland _ _ AP) as NS1.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (outlp, outlp + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 92)) in ACC'.
    unfold ctx_chunk, wz in CTX. unfold wz in OL. unfold adf_frame in FR.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 92) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|];
        apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_cons; [cbn [fst snd]; exact NSH| apply Forall_nil]]) end.
    step. ub_dead. step. ubal_by AL. step. if_lit.
    zstep. zstep. ck1f_load ACC a. step. if_false_by (ck1_bnez_false 0 eq_refl).
    step. step. step. if_lit.
    step. do 7 st1. step. step.
    release_frame FR ST (bv_unsigned sp). unfold ctx_chunk, wz. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma adf_call :
    forall (ra sp gp tp t0 t1 t2 s0 s1 x10 a1 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a outlp ov lo nn line : Z) (raw j : list byte),
      rw_cells asegs m a (ctx_chunk nn raw line) -> 0 < a -> a mod 16 = 0 -> a + 92 <= aceil -> aceil <= lo -> accessible m a 92 -> aapp a 92 -> 0 < nn < 2^31 ->
      rw_cells asegs m outlp [C4 (wz ov)] -> 0 < outlp -> outlp + 4 <= AAPP_HI -> (outlp + 4 <= lo \/ bv_unsigned sp <= outlp) -> (outlp + 4 <= a \/ a + 92 <= outlp) ->
      (outlp + 4 <= ALOWSH_LO \/ AHI_LO <= outlp) ->
      rw_cells asegs m (bv_unsigned sp + -64) (adf_frame j s5 s4 s3 s2 s1 s0 ra) ->
      stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (x10' : word) m1,
          ms' = MS (mkR (Z_to_bv 64 ADF_RA) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 outlp) (Z_to_bv 64 a) a1 (Z_to_bv 64 (a + 4)) (Z_to_bv 64 nn) (Z_to_bv 64 (-1)) a5 a6 a7
                       (Z_to_bv 64 a) (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.shiftr outlp 3 + 2147450880)) x10' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_evp_decodeblock_int) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -64, bv_unsigned sp); (outlp, outlp + 4)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -64) /\ rw_cells asegs m1 (bv_unsigned sp + -64) (adf_frame j s5 s4 s3 s2 s1 s0 ra)
          /\ rw_cells asegs m1 a (ctx_chunk nn raw line) /\ rw_cells asegs m1 outlp [C4 (wz 0)])
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 outlp) x10 a1 x12 a3 a4 a5 a6 a7
                 (Z_to_bv 64 a) s3 (Z_to_bv 64 (Z.shiftr outlp 3 + 2147450880)) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADF_J) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros CTX POS AL BL CEIL ACC0 AP NN OL OP OH OSEP OA NSH FR ST LO MI. unfold ADF_J, ADF_RA, P_evp_decodeblock_int.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold AAPP_HI in OH. pose proof (aapp_not_shadowland _ _ AP) as NS1.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (outlp, outlp + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 92)) in ACC'.
    unfold ctx_chunk, wz in CTX. unfold wz in OL. unfold adf_frame in FR.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 92) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|];
        apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_cons; [cbn [fst snd]; exact NSH| apply Forall_nil]]) end.
    step. ub_dead. step. ubal_by AL. step. if_lit.
    zstep. zstep. ck1f_load ACC a. step. if_false_by (ck1_bnez_false 0 eq_refl).
    st1. change (Z_to_bv 64 nn) with (wz nn). rewrite sx32_wz by lia. unfold wz. step. step. fbr.
    do 5 step. unfold ctx_chunk, wz, adf_frame. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma adf_ret :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 q1 q2 q4 q5 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (j : list byte),
      rw_cells asegs m (bv_unsigned sp + -64) (adf_frame j s5 s4 s3 s2 s1 s0 ra) ->
      stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom asegs)
          /\ stk asegs m lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 ADF_RA) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp q1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
                 q2 (Z_to_bv 64 (-1)) q4 q5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADF_RA)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros FR ST LO MI. unfold ADF_RA. pose proof (aword_range sp) as SPR. unfold adf_frame in FR.
    replace (ret_pc (Z_to_bv 64 0x422fc8)) with (Z_to_bv 64 0x422fc8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_lit. step. do 7 st1. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S2.

Section P.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma adecfinal_spec : decfinal_stmt H.
  Proof.
    unfold decfinal_stmt. intros until d. intros A0 A1 A2 EC TAB DC OL OSEP OA ACC OACC AC OSH OAL BL ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold DECFINAL_STACK, FR_EVP_DecodeFinal, DECBLOCK_STACK, FR_evp_decodeblock_int in LO. unfold ENCCTX_SIZE in *.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct EC as (raw & line & L80 & RD & CELLS & LR & EIN & EBR & DI).
    pose proof EBR as (POS & EAL & _ & _ & BLa & _ & EAP). unfold AIMG_TOP in *.
    pose proof (aapp_bounds a 92 EAP ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    pose proof OACC as (OP0 & OH & _). unfold AAPP_HI in OH.
    assert (OP : 0 < outlp) by (destruct OSH as [OSH|OSH]; [pose proof (aapp_bounds outlp 4 OSH ltac:(lia)); lia| lia]).
    assert (NSH : outlp + 4 <= ALOWSH_LO \/ AHI_LO <= outlp) by (destruct OSH as [OSH|OSH]; [exact (aapp_not_shadowland _ _ OSH)| right; unfold AHI_LO; lia]).
    assert (OAK : aconst_ok (outlp, outlp + 4)).
    { destruct OSH as [OSH|OSH]; [eapply aconst_ok_aapp; [exact OSH| cbn; lia| cbn; lia]| apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia]. }
    pose proof (ctx_chunk_of_enc _ _ _ _ _ CELLS) as CTX.
    unfold c8_post.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply adf_p1; [lia| exact OP| exact OAL| exact OACC| exact OSH| exact CEIL| exact AC| exact ST| lia| exact MI]|].
    intros ms1 (m1 & j & x10 & x12 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CTX1 : rw_cells asegs m1 a (ctx_chunk (zlength d) raw line)).
    { eapply rw_cells_transport; [exact CTX| exact MU1| exact WM1|]. unfold ctx_chunk. cbn [cells_size csize Nat.add length disjoint_from]. split; [lia| exact I]. }
    assert (OL1 : rw_cells asegs m1 outlp [C4 (wz ov)]).
    { eapply rw_cells_transport; [exact OL| exact MU1| exact WM1|]. cbn [cells_size csize Nat.add length disjoint_from]. split; [lia| exact I]. }
    assert (ACC1 : accessible m1 a 92).
    { eapply accessible_across; [exact ACC| exact MU1|]. apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_nil]. }
    destruct (Nat.eq_dec (length d) 0) as [D0|DN].
    - (* [comment removed for export] *)
      assert (d = []) as -> by (destruct d; [reflexivity| cbn in D0; lia]). change (zlength []) with 0 in CTX1.
      eapply evt_mono; [eapply adf_empty; [exact CTX1| lia| exact EAL| lia| exact CEIL| exact ACC1| exact EAP| exact OL1| exact OP| unfold AAPP_HI; lia| exact OSEP| exact OA| exact NSH| exact FR1| exact ST1| lia| exact MI1]|].
      intros ms' (x12' & x13' & m2 & -> & MU2 & WM2 & MI2 & ST2 & CTX2 & OL2).
      assert (MUall : munch [(lo, bv_unsigned sp); (outlp, outlp + 4)] m m2).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; intros z Hz; cbn in Hz |- *; lia. }
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m2. split; [reflexivity|].
      split; [unfold decode_final_rv; cbn; reflexivity|].
      split; [exact MUall|].
      split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|].
      split. { eapply ACONST_frame; [exact AC| exact MUall| eapply wmono_trans; [exact WM1| exact WM2]|].
               apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|]. apply Forall_cons; [exact OAK| apply Forall_nil]. }
      split; [exact ST2|].
      split. { exists raw, line. split; [exact L80|]. split; [exact RD|]. split; [apply enc_of_ctx_chunk; exact CTX2|].
               split; [exact LR|]. split; [exact EIN|]. split; [exact EBR| exact DI]. }
      split; [exact OL2| apply B64TAB_of_mem_inv; exact MI2].
    - (* [comment removed for export] *)
      assert (DM : Nat.modulo (length d) 4 <> 0%nat) by (destruct DC as [DC|DC]; [lia| exact DC]).
      pose proof DI as [DF D64].
      eapply evt_cut; [eapply adf_call; [exact CTX1| lia| exact EAL| lia| exact CEIL| exact ACC1| exact EAP| unfold zlength; lia| exact OL1| exact OP| unfold AAPP_HI; lia| exact OSEP| exact OA| exact NSH| exact FR1| exact ST1| lia| exact MI1]|].
      intros ms2 (x10' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FR2 & CTX2 & OL2).
      assert (ACC2 : accessible m2 a 92).
      { eapply accessible_across; [exact ACC1| exact MU2|]. apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_cons; [cbn [fst snd]; exact NSH| apply Forall_nil]]. }
      assert (MU12 : munch [(bv_unsigned sp + -64, bv_unsigned sp); (outlp, outlp + 4)] m m2).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| exact MU2]. intros z Hz; cbn in Hz |- *; lia. }
      assert (AC2 : ACONST m2).
      { eapply ACONST_frame; [exact AC| exact MU12| eapply wmono_trans; [exact WM1| exact WM2]|].
        apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|]. apply Forall_cons; [exact OAK| apply Forall_nil]. }
      eapply evt_cut.
      { eapply (adecblock_bad_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 a (zlength d) lo); rewrite ?unsigned_lit by lia.
        all: lazymatch goal with
             | |- rw_cells _ _ _ (ctx_chunk _ _ _) => exact CTX2
             | |- 0 < zlength _ <= 64 => unfold zlength; lia
             | |- 0 < _ => exact POS
             | |- _ mod 16 = 0 => exact EAL
             | |- _ + 92 <= aceil => lia
             | |- aceil <= _ => exact CEIL
             | |- accessible _ _ _ => exact ACC2
             | |- ACONST _ => exact AC2
             | |- Forall _ _ => unfold zlength; rewrite Nat2Z.id, RD; exact DF
             | |- bv_unsigned _ mod 2 = 0 => unfold ADF_RA; rewrite unsigned_lit by lia; reflexivity
             | |- not (_ mod 4 = 0) => unfold zlength; rewrite <- (Nat2Z.inj_mod _ 4); change (Z.of_nat 4) with 4; lia
             | |- stk _ _ _ _ => exact ST2
             | |- mem_inv _ _ => exact MI2
             | |- _ => unfold zlength; lia
             end. }
      intros ms3 PO. unfold adb_post in PO.
      destruct PO as (y0 & y1 & y2 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> & MU3 & WM3 & MI3 & ST3 & CTX3).
      rewrite (unsigned_lit (bv_unsigned sp + -64)) in MU3, ST3 by lia.
      apply (rw_cells_transport asegs _ m2 m3 _ _ FR2) in MU3 as FR3; [| exact WM3| cbn; lia].
      apply (rw_cells_transport asegs _ m2 m3 _ _ OL2) in MU3 as OL3; [| exact WM3| cbn; lia].
      eapply evt_mono; [eapply adf_ret; [exact FR3| exact ST3| lia| exact MI3]|].
      intros ms4 (-> & ST4).
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m3. split; [reflexivity|].
      split; [rewrite (decode_final_rv_bad d DI ltac:(lia) DM); reflexivity|].
      assert (MUall : munch [(lo, bv_unsigned sp); (outlp, outlp + 4)] m m3).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU12]| eapply munch_weaken; [| exact MU3]]; intros z Hz; cbn in Hz |- *; lia. }
      split; [exact MUall|].
      split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|].
      split. { eapply ACONST_frame; [exact AC| exact MUall| eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|].
               apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|]. apply Forall_cons; [exact OAK| apply Forall_nil]. }
      split; [exact ST4|].
      split. { exists raw, line. split; [exact L80|]. split; [exact RD|]. split; [apply enc_of_ctx_chunk; exact CTX3|].
               split; [exact LR|]. split; [exact EIN|]. split; [exact EBR| exact DI]. }
      split; [exact OL3| apply B64TAB_of_mem_inv; exact MI3].
     
  Qed.
End P.
