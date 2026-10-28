(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApBase ApPrim.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA AsStruct RtCallA UnwindA UnwindX EdgesA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRep ApFrame W_item_d2i_imgA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA Fr_i2o_SCT W_sct_completeA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
(* [comment removed for export] *)
Local Ltac nrm := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac ab_ichk t u J :=
  first [ match goal with OK : absh_ok _ _ _ |- _ => ab_join t u J OK end
        | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true] ].
Ltac lit_addr H := lazymatch type of H with
  | ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H
  | rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H end.
Ltac fz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Ltac thaw H := unfold frozen in H.

(* [comment removed for export] *)
Definition I2O_SCT_LEN_STACK_A : Z := IOS_FRAME + 48.      (* [comment removed for export] *)

Lemma swrap32_mod64' : forall i, -2^31 <= i < 2^31 -> bv_swrap 32 (i mod 2^64) = i.
Proof.
  intros i Hi. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (Z.div (2^32) 2) with (2^31).
  destruct (Z_lt_le_dec i 0) as [N|P].
  - assert (E : i mod 2^64 = i + 2^64).
    { rewrite <- (Z_mod_plus_full i 1 (2^64)). apply Z.mod_small. lia. }
    rewrite E. replace (i + 2^64 + 2^31) with (i + 2^31 + 2^32 * 2^32) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
  - rewrite (Z.mod_small i) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma v_addiw0_int : forall i, -2^31 <= i < 2^31 -> v_addiw (Z_to_bv 64 i) 0 = Z_to_bv 64 i.
Proof.
  intros i Hi. unfold v_addiw. f_equal. rewrite Z.add_0_r. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). apply swrap32_mod64'. exact Hi.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ios_head_cps : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo STK : Z)
    (adr : bptr -> Z) (sc : sctr bptr) (vs : Z),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + STK <= bv_unsigned sp -> I2O_SCT_LEN_STACK_A + RT_STACK <= STK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FRM < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB) -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctasegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) ->
  (forall (Σ1 : rts RT) (m4 : mem) (f spa : Z) (g : nat) (junk gj : list byte) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F' fc'
          (j0 j8 j16 j24 j32 j40 : list byte),
     @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m4 -> (forall b, In b (OW ++ LB) -> off_fr f 0 b) -> @fr_geo (push AR f 0) f 0 ->
     rt_credit RT Σ1 = rt_credit RT Σ - 1 -> rt_live RT Σ1 = rt_live RT Σ ->
     stk ctasegs m4 lo spa -> mem_inv ctasegs m4 ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m4 ->
     rw_cells ctasegs m4 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk] ->
     rw_cells ctasegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
     rw_cells ctasegs m4 (f + 32) [C8 (Z_to_bv 64 0)] ->
     rw_cells ctasegs m4 (shad f) ios_shadow_pro ->
     rw_cells ctasegs m4 (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) ->
     spa mod 32 = 0 -> bv_unsigned sp - 176 <= spa -> spa <= bv_unsigned sp - 160 ->
     Z.of_nat g = bv_unsigned sp - spa - 72 -> junk = gj ++ cells_bytes [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ->
     cps ctasegs (ASTA RT Σ1 PMc (eq
       (MS (mkR (Z_to_bv 64 0x3361dc) (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) (Z_to_bv 64 (bret (sct_complete sc))) x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 f) (Z_to_bv 64 (adr (sc_blk sc))) s4 s5 s6 a1 s8 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) x28 x29 x30 x31)
           F' (Z_to_bv 64 0x3361dc) fc' None m4 (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz I2O_SCT_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until vs. intros HEAP ST CEIL LO STKB TOP AL16 MI -> FLEN CRED HIN AL16S HX OK -> K.
  unfold I2O_SCT_LEN_STACK_A, IOS_FRAME in STKB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (XB0 & _ & _ & XBC & _). cbn [blk_addr blk_size fst snd] in *. nrm.
  change (wz I2O_SCT_A) with (wz IOS_ENTRY).
  eapply (ios_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold IOS_FRAME, RT_STACK; clear - LO STKB; lia| exact TOP| exact AL16| exact MI| reflexivity| exact FLEN| exact CRED|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 j16 j24 j32 j40 jf24 jf40
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold IOS_BODY, MallocRep.wz.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (CF1 & CF2 & CF3). nrm.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEIL LO0 LO STKB SPAL SPAH SPR; lia).
  pose proof (FRESH _ HIN) as OFX. unfold off_fr in OFX. change (fs_size 0) with 64 in OFX. cbn [blk_addr blk_size fst snd] in OFX.
  apply (rw_cells_agree _ _ _ _ _ AGF) in HX; [| intros xa Hxa; right; right; exists (sc_blk sc, adr (sc_blk sc), SCT_SIZE); split; [exact HIN| rewrite SctRep.sct_cells_size in Hxa; cbn; lia]].
  pose proof (rw_cells_app_l m3 (f + 32) [C8 (Z_to_bv 64 0)] _ (rw_cells_skip m3 f [_; _; _; _] _ 32 FRF eq_refl)) as HP. clear FRF.
  pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  fz G5.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep.
  eapply evt_cut.
  { eapply (@SCT_is_complete_specA (push AR f 0)) with (lo := lo) (adr := adr) (sc := sc) (vs := vs); rewrite ?ESPA;
      [exact HEAP3| exact ST3| exact MI3| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEIL| clear - LO STKB SPAL; lia| exact HIN| exact AL16S| exact HX| exact OK| reflexivity]. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m4 & -> & MU4 & WM4 & MI4 & ST4). rewrite ?ESPA in *.
  rewrite (ret_pc_even 0x3361dc) by (clear; lia).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in FRL; [| cbn; clear; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in FRH; [| cbn; clear - SPAH; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HP; [| cbn; clear - G3 CEIL LO STKB SPAL; lia].
  thaw G5. apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in FRS; [| cbn; unfold shad, SHB; clear - G3 G5 CF2 CF3 CEIL LO STKB SPAL; Z.div_mod_to_equations; lia]. fz G5.
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HX; [| rewrite SctRep.sct_cells_size; cbn; clear - XBC CEIL LO STKB SPAL; lia].
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m4).
  { eapply (@AH_frame (push AR f 0)); [exact HEAP3| exact MU4| exact WM4|]. constructor; [left; cbn [fst snd]; clear - CEIL LO STKB SPAL SPAH TOP; plia| constructor]. }
  apply evt_done.
  eapply (K Σ1 m4 f spa g junk gj); try eassumption.
  - eapply agree_on_trans; [exact AGF|]. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)|]. intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH; lia| |].
    + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL CE1 LO STKB SPAL; lia.
    + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, B3'. clear - Hr B3' CEIL LO STKB SPAL. plia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2o_sct_len_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo STK : Z)
    (adr : bptr -> Z) (sc : sctr bptr) (vs : Z),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + STK <= bv_unsigned sp -> I2O_SCT_LEN_STACK_A + RT_STACK <= STK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FRM < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB) -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctasegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc -> sct_complete sc = true ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) -> a1 = Z_to_bv 64 0 ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 1 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m' ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 (i2o_sct_len sc)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz I2O_SCT_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until vs. intros HEAP ST CEIL LO STKB TOP AL16 MI TP FLEN CRED HIN AL16S HX OK CPL -> -> K.
  pose proof STKB as STKB'. unfold I2O_SCT_LEN_STACK_A, IOS_FRAME in STKB'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (XB0 & _ & _ & XBC & _). cbn [blk_addr blk_size fst snd] in *.
  pose proof OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  assert (SL : 0 <= sc_siglen sc <= 65535) by (unfold sc_siglen; destruct (sc_sig sc) as [[q n]|] eqn:ES; [pose proof (SIGP q n eq_refl); lia| lia]).
  clear SIGP BLOBP LOGP EXTP EXTL BLBL. nrm.
  eapply (ios_head_cps Q) with (lo := lo) (STK := STK) (OW := OW) (LB := LB) (adr := adr) (sc := sc) (vs := vs); try eassumption; try reflexivity.
  intros Σ1 m4 f spa g junk gj x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F1 fc1 j0 j8 j16 j24 j32 j40
         HEAP4 FRESH GEO CR1 EL1 ST4 MI4 AG4 FRL FRH HP FRS HX4 SPA32 SPAL SPAH GSZ SAVJ.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP4) as (CF1 & CF2 & CF3). nrm.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEIL LO0 LO STKB' SPAL SPAH SPR; lia).
  ablock HEAP4 HIN ACCX OFFX. fz OFFX. unfold SCT_SIZE in *.
  unfold sct_cells, MallocRep.wz, u32 in HX4.
  pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
  fz G5. rewrite CPL. cbn [bret].
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. bnot. zstep. rewrite sx32_mod32 by (clear - VR; lia). zstep. if_cases KV; zify_cond KV.
  - (* [comment removed for export] *)
    assert (V0 : sc_version sc = 0) by (destruct VR as [E0|VR']; [exfalso; revert KV; rewrite E0; vm_compute; congruence| revert KV; rewrite land64_small by lia; intros KV; lia]).
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. rewrite (Z.shiftr_div_pow2 _ 31), Z.div_small by (clear - ELR SL; lia). zstep. btaken. zstep. btaken.
    apply evt_done. change (Z_to_bv 64 3367600) with (wz IOS_EXIT).
    eapply (@ios_epi_cps AR Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAP4| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST4| exact CEIL| clear - LO STKB' SPAL; lia
      | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI4| exact FRL| exact FRH| reflexivity|].
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    rewrite (v_addiw0_int (sc_extlen sc + 47 + sc_siglen sc)) by (clear - ELR SL; lia).
    replace (sc_extlen sc + 47 + sc_siglen sc) with (i2o_sct_len sc) by (unfold i2o_sct_len; rewrite V0; cbn [Z.eqb]; clear; lia).
    eapply K; [exact HEAP'| rewrite CR'; exact CR1| rewrite LIVE'; exact EL1| exact ST'| exact MI'|].
    eapply agree_on_trans; [exact AG4|]. eapply agree_on_mono; [exact AG'|]. intros a Ha.
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
  - (* [comment removed for export] *)
    assert (VN : sc_version sc <> 0) by (intros E0; apply KV; rewrite E0; reflexivity).
    zstep. zstep. zstep. rewrite (Z.shiftr_div_pow2 _ 31), Z.div_small by (clear - BLR; lia). zstep. btaken. zstep. btaken.
    apply evt_done. change (Z_to_bv 64 3367600) with (wz IOS_EXIT).
    eapply (@ios_epi_cps AR Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAP4| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST4| exact CEIL| clear - LO STKB' SPAL; lia
      | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI4| exact FRL| exact FRH| reflexivity|].
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    rewrite (v_addiw0_int (sc_bloblen sc)) by (clear - BLR; lia).
    replace (sc_bloblen sc) with (i2o_sct_len sc) by (unfold i2o_sct_len; replace (sc_version sc =? 0) with false by (symmetry; apply Z.eqb_neq; exact VN); reflexivity).
    eapply K; [exact HEAP'| rewrite CR'; exact CR1| rewrite LIVE'; exact EL1| exact ST'| exact MI'|].
    eapply agree_on_trans; [exact AG4|]. eapply agree_on_mono; [exact AG'|]. intros a Ha.
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
Qed.

End WithRT.
