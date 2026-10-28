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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA AsStruct RtCallA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRep ApFrame W_item_d2i_imgA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA Fr_asn1_ex_i2c Fr_asn1_i2d_ex_primitive W_asn1_enc_leavesA W_asn1_ex_i2cA.
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
Definition ASN1_I2D_EX_PRIM_STACK_A : Z := AIP_FRAME + ASN1_EX_I2C_STACK_A.
Definition AIP_OUT : Z := 0x24878c.      (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma aip_open_utype : forall Σ1 OW LB m3 f q,
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 0 b) -> @fr_geo (push AR f 0) f 0 ->
  rw_cells ctasegs m3 (shad f) aip_shadow_pro -> ~ In q (map blk_id (OW ++ LB)) ->
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((q, f + 32, 4) :: LB) m3.
Proof.
  intros Σ1 OW LB m3 f q HEAP FRESH GEO FRS Hq.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 0) Σ1 OW LB m3 f 0%nat q (f + 32) 4 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 0) with 64; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m3 (shad f) aip_shadow_pro 4%nat (f + 32) 4 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 0) with 64 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aip_len_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (PVAL A len D fl : Z) (bPV bA : block),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + ASN1_I2D_EX_PRIM_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> fr_depth_ok 2%nat -> 2 <= rt_credit RT Σ ->
  In bPV (OW ++ LB) -> blk_addr bPV <= PVAL -> PVAL + 8 <= blk_addr bPV + blk_size bPV -> PVAL mod 8 = 0 -> rw_cells ctasegs m PVAL [C8 (wz A)] ->
  In bA (OW ++ LB) -> blk_addr bA <= A -> A + ASN1_STRING_SIZE <= blk_addr bA + blk_size bA -> A mod 8 = 0 ->
  rw_cells ctasegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  0 <= len < 65536 -> 0 <= D < 2^64 -> 0 <= fl < 2^64 ->
  a0 = wz PVAL -> a1 = wz 0 -> a2 = wz ITEM_OCTET_A -> a3 = Z_to_bv 64 (-1) -> a4 = wz 0 ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 2 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m' ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 (der_hl len + len)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_I2D_EX_PRIMITIVE_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until bA. intros HEAP ST CEIL LO TOP AL16 MI -> FD CRED PVIN PVL PVH PVAL8 HPV AIN AL AH A8 HS LEN DR FLR -> -> -> -> -> K.
  unfold ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AIP_FRAME, AEI_FRAME in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PVIN) as (VB0 & _ & _ & VBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP AIN) as (AB0 & _ & _ & ABC & _). cbn [blk_addr blk_size fst snd] in *. nrm.
  destruct (fr_depth_push 1%nat 0 0%nat FD) as [FLEN _].
  change (wz ASN1_I2D_EX_PRIMITIVE_A) with (wz AIP_ENTRY).
  eapply (aip_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold AIP_FRAME, RT_STACK; clear - LO; lia| exact TOP| exact AL16| vm_compute; reflexivity (* [comment removed for export] *)| exact MI| reflexivity| exact FLEN| clear - CRED; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 j16 j32 j40 j48 jf24 jf32 jf36
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold AIP_BODY, MallocRep.wz. rewrite !(unsigned_lit ITEM_OCTET_A) by (unfold ITEM_OCTET_A; clear; lia).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
  destruct (fr_depth_push 1%nat f 0%nat FD) as [_ FD1]. destruct (@fr_depth_push (push AR f 0) 0%nat 0 0%nat FD1) as [FLEN1 _].
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (CF1 & CF2 & CF3). nrm.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CF3; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEIL LO0 LO SPAL SPAH SPR; lia).
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [q Hq].
  pose proof (aip_open_utype Σ1 OW LB m3 f q HEAP3 FRESH GEO FRS Hq) as HEAPo.
  set (LB' := (q, f + 32, 4) :: LB) in HEAPo.
  assert (INC : forall b, In b (OW ++ LB) -> In b (OW ++ LB')) by (intros b Hb; apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]).
  assert (QIN : In (q, f + 32, 4) (OW ++ LB')) by (apply in_or_app; right; left; reflexivity).
  pose proof (FRESH _ PVIN) as OFV. pose proof (FRESH _ AIN) as OFA. unfold off_fr in OFV, OFA. change (fs_size 0) with 64 in OFV, OFA.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPV; [| intros xa Hxa; right; right; exists bPV; split; [exact PVIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HS; [| intros xa Hxa; right; right; exists bA; split; [exact AIN| unfold asn1_string_cells, ASN1_STRING_SIZE in *; cbn in Hxa; lia]].
  (* [comment removed for export] *)
  pose proof (item_octA_of_heap _ _ _ _ _ HEAP3) as ((I1 & I2 & I3 & I4 & I5 & ACCI) & I7). unfold ITEM_OCTET_A in *.
  lit_addr I2. lit_addr I3. lit_addr I4. lit_addr I5. lit_addr I7.
  unfold asn1_string_cells, ASN1_STRING_SIZE, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  pose proof (munch_refl [(spa, spa + 56); (f + 32, f + 36)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  assert (OFFW : offshW [(spa, spa + 56); (f + 32, f + 36)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - CF1 CF2 CEIL LO SPAL G4 G5; lia).
  assert (AWO : Forall (@aclient_write_ok (push AR f 0) (OW ++ LB')) [(spa, spa + 56); (f + 32, f + 36)]%Z).
  { constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia|].
    constructor; [right; right; exists (q, f + 32, 4); split; [exact QIN| cbn; clear; lia]| constructor]. }
  fz G5.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  ab_shload 8. rewrite ?zxb_z8. step. step. first [if_false | if_true]. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite ?zxb_z8.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  match goal with H : munch _ m3 m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs m3 m4 |- _ => rename H into WM4 end.
  match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4 end.
  match goal with H : rw_cells ctasegs m4 f _ |- _ => rename H into FRF4 end. match goal with H : rw_cells ctasegs m4 spa _ |- _ => rename H into FRL4 end.
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' m4) by (eapply (@AH_frame (push AR f 0)); [exact HEAPo| exact MU4| exact WM4| exact AWO]).
  assert (ST4 : stk ctasegs m4 lo spa) by (first [assumption| eapply stk_transport; [exact ST3| exact MU4| exact WM4| cbn; clear; lia]]).
  pose proof (rw_cells_app_l m4 (f + 32) [C4 (Z_to_bv 64 4)] _ (rw_cells_skip m4 f [_; _; _; _] _ 32 FRF4 eq_refl)) as HPU.
  apply evt_done.
  eapply (@asn1_ex_i2c_len_cpsA (push AR f 0) Q) with (lo := lo) (OW := OW) (LB := LB') (PVAL := PVAL) (PUT := f + 32) (A := A) (len := len) (D := D) (fl := fl)
    (bPV := bPV) (bPU := (q, f + 32, 4)) (bA := bA); rewrite ?ESPA; try reflexivity.
  - exact HEAP4.
  - exact ST4.
  - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
  - unfold ASN1_EX_I2C_STACK_A, AEI_FRAME, RT_STACK. clear - LO SPAL. lia.
  - unfold USTACK_TOP. clear - TOP SPAH. lia.
  - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
  - exact MI4.
  - exact FLEN1.
  - cbn [ar_RT push amb]. clear - CRED CR1. lia.
  - exact (INC _ PVIN).
  - exact PVL.
  - exact PVH.
  - clear - PVAL8. uchk_open. exact PVAL8.
  - exact HPV.
  - exact QIN.
  - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
  - exact HPU.
  - exact (INC _ AIN).
  - exact AL.
  - unfold ASN1_STRING_SIZE. exact AH.
  - clear - A8. uchk_open. exact A8.
  - exact HS.
  - clear - LEN; lia.
  - exact DR.
  - exact FLR.
  - (* [comment removed for export] *)
    intros Σ2 m5 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 HEAP5 CR2 EL2 ST5 MI5 AG5.
    cbn [ar_RT push amb] in CR2, EL2. rewrite (ret_pc_even 0x248738) by (clear; lia).
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRL4; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRH; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HPU; [| intros xa Hxa; cbn in Hxa; right; right; exists (q, f + 32, 4); split; [exact QIN| cbn; clear - Hxa; lia]].
    pose proof (munch_refl [(spa, spa + 56)]%Z m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep. sfalse. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. btaken.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (len + 2 <? 1) with false by (symmetry; apply Z.ltb_ge; clear - LEN; lia). cbn [Z.b2z].
    change (Z.shiftl 0 1) with 0. change (Z.land (bv_swrap 32 (0 + -1)) 18446744073709551615) with 18446744073709551615.
    rewrite (Z.land_comm 18446744073709551615 len), (land64_small len) by (clear - LEN; lia).
    zstep. zstep. zstep. btaken.
    (* [comment removed for export] *)
    zstep. bnot. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : munch _ m5 m6 |- _ => rename H into MU6 end. match goal with H : wmono ctasegs m5 m6 |- _ => rename H into WM6 end.
    match goal with H : mem_inv ctasegs m6 |- _ => rename H into MI6 end. match goal with H : rw_cells ctasegs m6 spa _ |- _ => rename H into FRL6 end.
    assert (ST6 : stk ctasegs m6 lo spa) by (first [assumption| eapply stk_transport; [exact ST5| exact MU6| exact WM6| cbn; clear; lia]]).
    eapply evt_cut.
    { eapply ASN1_object_size_specA with (lo := lo) (len := len); rewrite ?ESPA; [exact ST6| exact MI6| clear - LO SPAL; lia| exact LEN| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros ms7 PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m7 & -> & MU7 & WM7 & MI7 & ST7). rewrite ?ESPA in *.
    rewrite (ret_pc_even 0x248820) by (clear; lia).
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in FRL6; [| cbn; clear; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in FRH; [| cbn; clear - SPAH; lia].
    assert (MU57 : munch [(spa - 16, spa + 56)]%Z m5 m7).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU6]| eapply munch_weaken; [| exact MU7]]; unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
    assert (WM57 : wmono ctasegs m5 m7) by (eapply wmono_trans; [exact WM6| exact WM7]).
    assert (HEAP7 : @BnHeapA.AHEAP (push AR f 0) Σ2 OW LB' m7).
    { eapply (@AH_frame (push AR f 0)); [exact HEAP5| exact MU57| exact WM57|]. constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia| constructor]. }
    (* [comment removed for export] *)
    zstep.
    apply evt_done. change (Z_to_bv 64 2394148) with (wz AIP_EXIT).
    eapply (@frame_obj_close (push AR f 0)) in HEAP7; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; clear; lia].
    eapply (@aip_epi_cps AR Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAP7| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST7| exact CEIL| clear - LO SPAL; lia
      | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI7
      | exact (rw_cells_cb_first m7 spa _ 6 FRL6)| exact FRH| reflexivity|].
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    eapply K; [exact HEAP'| rewrite CR', CR2; exact ltac:(clear - CR1; lia)| rewrite LIVE', EL2; exact EL1| exact ST'| exact MI'|].
    (* [comment removed for export] *)
    assert (OUTW : forall a lo' hi', aclient_addr (OW ++ LB) (bv_unsigned sp) a -> spa - 16 <= lo' -> hi' <= spa + 56 ->
              outside [(lo', hi'); (f + 32, f + 36)]%Z a).
    { intros a lo' hi' Ha Hl Hh. cbn [outside fst snd]. thaw G5.
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
      - clear - Ha Hl Hh SPAH G3 CEIL LO. repeat split; try exact I; lia.
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr Hl Hh CEIL CE1 LO SPAL G4; repeat split; try exact I; lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 0) with 64 in O.
        destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, O, B3'. clear - Hr Hl Hh B3' O CEIL LO SPAL. repeat split; try exact I; plia. }
    eapply agree_on_trans; [exact AGF|].
    eapply agree_on_trans.
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)|]. intros a Ha. apply (OUTW a); [exact Ha| clear; lia| clear; lia]. }
    eapply agree_on_trans.
    { eapply agree_on_mono; [exact AG5|]. intros a Ha.
      destruct Ha as [Ha1|[Ha1|(b & Hb & Hr)]]; [left; clear - Ha1 SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha1| right; right; exists b; split; [exact (INC b Hb)| exact Hr]]. }
    eapply agree_on_trans.
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU57)|]. intros a Ha.
      pose proof (OUTW a (spa - 16) (spa + 56) Ha ltac:(clear; lia) ltac:(clear; lia)) as X. cbn [outside fst snd] in X |- *. clear - X. tauto. }
    eapply agree_on_mono; [exact AG'|]. intros a Ha.
    destruct Ha as [Ha1|[Ha1|Ha1]]; [left; clear - Ha1 SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha1| right; right; exact Ha1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aip_write_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (PVAL A len D fl PP P : Z) (src j1 j2 : list byte) (bPV bA bPP bP bD : block),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + ASN1_I2D_EX_PRIM_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> fr_depth_ok 2%nat -> 3 <= rt_credit RT Σ ->
  In bPV (OW ++ LB) -> blk_addr bPV <= PVAL -> PVAL + 8 <= blk_addr bPV + blk_size bPV -> PVAL mod 8 = 0 -> rw_cells ctasegs m PVAL [C8 (wz A)] ->
  In bA (OW ++ LB) -> blk_addr bA <= A -> A + ASN1_STRING_SIZE <= blk_addr bA + blk_size bA -> A mod 8 = 0 ->
  rw_cells ctasegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  0 < len < 65536 -> 0 <= fl < 2^64 ->
  In bPP (OW ++ LB) -> blk_addr bPP <= PP -> PP + 8 <= blk_addr bPP + blk_size bPP -> PP mod 8 = 0 -> rw_cells ctasegs m PP [C8 (wz P)] ->
  In bP (OW ++ LB) -> blk_addr bP <= P -> P + der_hl len + len <= blk_addr bP + blk_size bP ->
  rw_cells ctasegs m P [CB (Z.to_nat (der_hl len)) j1] -> rw_cells ctasegs m (P + der_hl len) [CB (Z.to_nat len) j2] ->
  In bD (OW ++ LB) -> blk_addr bD <= D -> D + len <= blk_addr bD + blk_size bD -> bytes_at ctasegs m D src -> length src = Z.to_nat len ->
  (PP + 8 <= P \/ P + der_hl len + len <= PP) -> (D + len <= P \/ P + der_hl len + len <= D) ->
  (A + ASN1_STRING_SIZE <= P \/ P + der_hl len + len <= A) -> (PVAL + 8 <= P \/ P + der_hl len + len <= PVAL) ->
  (PVAL + 8 <= PP \/ PP + 8 <= PVAL) -> (A + ASN1_STRING_SIZE <= PP \/ PP + 8 <= A) -> (D + len <= PP \/ PP + 8 <= D) ->
  a0 = wz PVAL -> a1 = wz PP -> a2 = wz ITEM_OCTET_A -> a3 = Z_to_bv 64 (-1) -> a4 = wz 0 ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 3 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(P, P + der_hl len + len); (PP, PP + 8)]%Z a) m m' ->
     rw_cells ctasegs m' PP [C8 (wz (P + der_hl len + len))] ->
     (exists hb, rw_cells ctasegs m' P [CB (Z.to_nat (der_hl len)) hb]) -> rw_cells ctasegs m' (P + der_hl len) [CB (Z.to_nat len) src] ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 (der_hl len + len)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_I2D_EX_PRIMITIVE_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until bD. intros HEAP ST CEIL LO TOP AL16 MI -> FD CRED PVIN PVL PVH PVAL8 HPV AIN AL AH A8 HS LEN FLR
         PPIN PPL PPH PP8 HPP PIN PL PH HP1 HP2 DIN DL DH SRC SLEN SEPP SEPD SEPA SEPV SEPVP SEPAP SEPDP -> -> -> -> -> K.
  unfold ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AIP_FRAME, AEI_FRAME in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (der_hl_range len ltac:(clear - LEN; lia)) as HLR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PVIN) as (VB0 & _ & _ & VBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP AIN) as (AB0 & _ & _ & ABC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PPIN) as (QB0 & _ & _ & QBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PIN) as (PB0 & _ & _ & PBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP DIN) as (DB0 & _ & _ & DBC & _). cbn [blk_addr blk_size fst snd] in *. nrm.
  assert (DR : 0 <= D < 2^64) by (clear - DB0 DL DH DBC CE3 LEN; lia).
  unfold ASN1_STRING_SIZE in SEPA, SEPAP. fz SEPP. fz SEPD. fz SEPA. fz SEPV. fz SEPVP. fz SEPAP. fz SEPDP.
  destruct (fr_depth_push 1%nat 0 0%nat FD) as [FLEN _].
  change (wz ASN1_I2D_EX_PRIMITIVE_A) with (wz AIP_ENTRY).
  eapply (aip_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold AIP_FRAME, RT_STACK; clear - LO; lia| exact TOP| exact AL16| vm_compute; reflexivity (* [comment removed for export] *)| exact MI| reflexivity| exact FLEN| clear - CRED; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 j16 j32 j40 j48 jf24 jf32 jf36
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold AIP_BODY, MallocRep.wz. rewrite !(unsigned_lit ITEM_OCTET_A) by (unfold ITEM_OCTET_A; clear; lia).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
  destruct (fr_depth_push 1%nat f 0%nat FD) as [_ FD1]. destruct (@fr_depth_push (push AR f 0) 0%nat 0 0%nat FD1) as [FLEN1 _].
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (CF1 & CF2 & CF3). nrm.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CF3; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEIL LO0 LO SPAL SPAH SPR; lia).
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [q Hq].
  pose proof (aip_open_utype Σ1 OW LB m3 f q HEAP3 FRESH GEO FRS Hq) as HEAPo.
  set (LB' := (q, f + 32, 4) :: LB) in HEAPo.
  assert (INC : forall b, In b (OW ++ LB) -> In b (OW ++ LB')) by (intros b Hb; apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]).
  assert (QIN : In (q, f + 32, 4) (OW ++ LB')) by (apply in_or_app; right; left; reflexivity).
  pose proof (FRESH _ PVIN) as OFV. pose proof (FRESH _ AIN) as OFA. pose proof (FRESH _ PPIN) as OFQ. pose proof (FRESH _ PIN) as OFP. pose proof (FRESH _ DIN) as OFD.
  unfold off_fr in OFV, OFA, OFQ, OFP, OFD. change (fs_size 0) with 64 in OFV, OFA, OFQ, OFP, OFD.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPV; [| intros xa Hxa; right; right; exists bPV; split; [exact PVIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HS; [| intros xa Hxa; right; right; exists bA; split; [exact AIN| unfold asn1_string_cells, ASN1_STRING_SIZE in *; cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPP; [| intros xa Hxa; right; right; exists bPP; split; [exact PPIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HP1; [| intros xa Hxa; right; right; exists bP; split; [exact PIN| cbn [cells_size csize] in Hxa; rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HP2; [| intros xa Hxa; right; right; exists bP; split; [exact PIN| cbn [cells_size csize] in Hxa; rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia; lia]].
  apply (bytes_at_agree _ m m3 _ _ AGF) in SRC; [| intros xa Hxa; rewrite SLEN, Z2Nat.id in Hxa by lia; right; right; exists bD; split; [exact DIN| lia]].
  fz HP1. fz HP2. assert (SRCF : frozen (bytes_at ctasegs m3 D src)) by exact SRC. clear SRC.
  (* [comment removed for export] *)
  pose proof (item_octA_of_heap _ _ _ _ _ HEAP3) as ((I1 & I2 & I3 & I4 & I5 & ACCI) & I7). unfold ITEM_OCTET_A in *.
  lit_addr I2. lit_addr I3. lit_addr I4. lit_addr I5. lit_addr I7.
  pose proof (INC _ PPIN) as PPIN'. ablock HEAPo PPIN' ACCQ OFFQ. fz OFFQ.
  unfold asn1_string_cells, ASN1_STRING_SIZE, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  pose proof (munch_refl [(spa, spa + 56); (f + 32, f + 36)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  assert (OFFW : offshW [(spa, spa + 56); (f + 32, f + 36)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - CF1 CF2 CEIL LO SPAL G4 G5; lia).
  assert (AWO : Forall (@aclient_write_ok (push AR f 0) (OW ++ LB')) [(spa, spa + 56); (f + 32, f + 36)]%Z).
  { constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia|].
    constructor; [right; right; exists (q, f + 32, 4); split; [exact QIN| cbn; clear; lia]| constructor]. }
  fz G5.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  ab_shload 8. rewrite ?zxb_z8. step. step. first [if_false | if_true]. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite ?zxb_z8.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  match goal with H : munch _ m3 m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs m3 m4 |- _ => rename H into WM4 end.
  match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4 end.
  match goal with H : rw_cells ctasegs m4 f _ |- _ => rename H into FRF4 end. match goal with H : rw_cells ctasegs m4 spa _ |- _ => rename H into FRL4 end.
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' m4) by (eapply (@AH_frame (push AR f 0)); [exact HEAPo| exact MU4| exact WM4| exact AWO]).
  assert (ST4 : stk ctasegs m4 lo spa) by (first [assumption| eapply stk_transport; [exact ST3| exact MU4| exact WM4| cbn; clear; lia]]).
  pose proof (rw_cells_app_l m4 (f + 32) [C4 (Z_to_bv 64 4)] _ (rw_cells_skip m4 f [_; _; _; _] _ 32 FRF4 eq_refl)) as HPU.
  apply evt_done.
  eapply (@asn1_ex_i2c_len_cpsA (push AR f 0) Q) with (lo := lo) (OW := OW) (LB := LB') (PVAL := PVAL) (PUT := f + 32) (A := A) (len := len) (D := D) (fl := fl)
    (bPV := bPV) (bPU := (q, f + 32, 4)) (bA := bA); rewrite ?ESPA; try reflexivity.
  - exact HEAP4.
  - exact ST4.
  - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
  - unfold ASN1_EX_I2C_STACK_A, AEI_FRAME, RT_STACK. clear - LO SPAL. lia.
  - unfold USTACK_TOP. clear - TOP SPAH. lia.
  - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
  - exact MI4.
  - exact FLEN1.
  - cbn [ar_RT push amb]. clear - CRED CR1. lia.
  - exact (INC _ PVIN).
  - exact PVL.
  - exact PVH.
  - clear - PVAL8. uchk_open. exact PVAL8.
  - exact HPV.
  - exact QIN.
  - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
  - exact HPU.
  - exact (INC _ AIN).
  - exact AL.
  - unfold ASN1_STRING_SIZE. exact AH.
  - clear - A8. uchk_open. exact A8.
  - exact HS.
  - clear - LEN; lia.
  - exact DR.
  - exact FLR.
  - (* [comment removed for export] *)
    intros Σ2 m5 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 HEAP5 CR2 EL2 ST5 MI5 AG5.
    cbn [ar_RT push amb] in CR2, EL2. rewrite (ret_pc_even 0x248738) by (clear; lia).
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRL4; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRH; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HPU; [| intros xa Hxa; cbn in Hxa; right; right; exists (q, f + 32, 4); split; [exact QIN| cbn; clear - Hxa; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HPV; [| intros xa Hxa; cbn in Hxa; right; right; exists bPV; split; [exact (INC _ PVIN)| clear - Hxa PVL PVH; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HS; [| intros xa Hxa; cbn in Hxa; right; right; exists bA; split; [exact (INC _ AIN)| clear - Hxa AL AH; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HPP; [| intros xa Hxa; cbn in Hxa; right; right; exists bPP; split; [exact (INC _ PPIN)| clear - Hxa PPL PPH; lia]].
    thaw HP1. thaw HP2.
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HP1; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; clear - PBC PL PH HLR LEN CEIL LO SPAL OFP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HP1; [| intros xa Hxa; cbn [cells_size csize] in Hxa; rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia; right; right; exists bP; split; [exact (INC _ PIN)| clear - Hxa PL PH HLR LEN; lia]].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HP2; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; clear - PBC PL PH HLR LEN CEIL LO SPAL OFP; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HP2; [| intros xa Hxa; cbn [cells_size csize] in Hxa; rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia; right; right; exists bP; split; [exact (INC _ PIN)| clear - Hxa PL PH HLR LEN; lia]].
    assert (SRC5 : bytes_at ctasegs m5 D src).
    { pose proof SRCF as X. thaw X. apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU4) in X; [| rewrite SLEN, Z2Nat.id by lia; cbn; clear - DBC DL DH LEN CEIL LO SPAL OFD; lia].
      eapply bytes_at_agree; [exact AG5| exact X|]. intros xa Hxa. rewrite SLEN, Z2Nat.id in Hxa by lia. right; right; exists bD; split; [exact (INC _ DIN)| clear - Hxa DL DH; lia]. }
    clear SRCF. fz HP2. assert (SRCF : frozen (bytes_at ctasegs m5 D src)) by exact SRC5. clear SRC5.
    pose proof (munch_refl [(spa, spa + 56)]%Z m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep. sfalse. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. btaken.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (len + 2 <? 1) with false by (symmetry; apply Z.ltb_ge; clear - LEN; lia). cbn [Z.b2z].
    change (Z.shiftl 0 1) with 0. change (Z.land (bv_swrap 32 (0 + -1)) 18446744073709551615) with 18446744073709551615.
    rewrite (Z.land_comm 18446744073709551615 len), (land64_small len) by (clear - LEN; lia).
    zstep. zstep. zstep. sfalse.
    (* [comment removed for export] *)
    zstep. bnot. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : munch _ m5 m6 |- _ => rename H into MU6 end. match goal with H : wmono ctasegs m5 m6 |- _ => rename H into WM6 end.
    match goal with H : mem_inv ctasegs m6 |- _ => rename H into MI6 end. match goal with H : rw_cells ctasegs m6 spa _ |- _ => rename H into FRL6 end.
    assert (ST6 : stk ctasegs m6 lo spa) by (first [assumption| eapply stk_transport; [exact ST5| exact MU6| exact WM6| cbn; clear; lia]]).
    assert (HEAP6 : @BnHeapA.AHEAP (push AR f 0) Σ2 OW LB' m6).
    { eapply (@AH_frame (push AR f 0)); [exact HEAP5| exact MU6| exact WM6|]. constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia| constructor]. }
    thaw HP1. thaw SEPP.
    eapply evt_cut.
    { eapply (@ASN1_put_object_specA (push AR f 0)) with (lo := lo) (len := len) (PP := PP) (P := P) (junk := j1) (OW := OW) (LB := LB'); rewrite ?ESPA; try reflexivity.
      - exact HEAP6.
      - exact ST6.
      - exact MI6.
      - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
      - clear - LO SPAL; lia.
      - clear - LEN; lia.
      - exists bPP. split; [exact (INC _ PPIN)| cbn; clear - PPL PPH; lia].
      - clear - PP8. uchk_open. exact PP8.
      - exists bP. split; [exact (INC _ PIN)| cbn; clear - PL PH HLR LEN; lia].
      - clear - SEPP HLR LEN. lia.
      - exact HPP.
      - exact HP1. }
    fz SEPP. clear HP1.
    cbv beta. intros ms7 PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m7 & -> & MU7 & WM7 & MI7 & ST7 & HPP7 & (hb & HP17)). rewrite ?ESPA in *.
    rewrite (ret_pc_even 0x2487a4) by (clear; lia). unfold MallocRep.wz in HPP7.
    (* [comment removed for export] *)
    thaw SEPP. thaw SEPV. thaw SEPVP. thaw SEPA. thaw SEPAP. thaw SEPD. thaw SEPDP. thaw HP2.
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in FRL6; [| cbn; clear - QBC PPH PBC PH HLR LEN CEIL LO SPAL; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in FRH; [| cbn; clear - QBC PPH PBC PH HLR LEN CEIL LO SPAL SPAH; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in HPU; [| cbn; clear - OFQ OFP PPL PPH PL PH HLR LEN G3 CEIL LO SPAL; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in HPV; [| cbn; clear - SEPV SEPVP VBC PVH HLR LEN CEIL LO SPAL; lia].
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU7 WM7) in HS; [| cbn; clear - SEPA SEPAP ABC AH HLR LEN CEIL LO SPAL; lia].
    assert (MU57 : munch [(spa - 16, spa + 56); (P, P + der_hl len); (PP, PP + 8)]%Z m5 m7).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU6]| eapply munch_weaken; [| exact MU7]]; unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
    assert (WM57 : wmono ctasegs m5 m7) by (eapply wmono_trans; [exact WM6| exact WM7]).
    apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU57 WM57) in HP2; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; clear - SEPP PBC PH HLR LEN CEIL LO SPAL; lia].
    assert (SRC7 : bytes_at ctasegs m7 D src).
    { pose proof SRCF as X. thaw X. apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU57) in X; [exact X|]. rewrite SLEN, Z2Nat.id by lia. cbn. clear - SEPD SEPDP DBC DH HLR LEN CEIL LO SPAL. lia. }
    clear SRCF. fz SEPP. fz SEPV. fz SEPVP. fz SEPA. fz SEPAP. fz SEPD. fz SEPDP.
    assert (AWO7 : Forall (@aclient_write_ok (push AR f 0) (OW ++ LB')) [(spa - 16, spa + 56); (P, P + der_hl len); (PP, PP + 8)]%Z).
    { constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia|].
      constructor; [right; right; exists bP; split; [exact (INC _ PIN)| cbn; clear - PL PH HLR LEN; lia]|].
      constructor; [right; right; exists bPP; split; [exact (INC _ PPIN)| cbn; clear - PPL PPH; lia]| constructor]. }
    assert (HEAP7 : @BnHeapA.AHEAP (push AR f 0) Σ2 OW LB' m7) by (eapply (@AH_frame (push AR f 0)); [exact HEAP5| exact MU57| exact WM57| exact AWO7]).
    clear MU6 WM6 MU7 WM7 ST6 MI6 HEAP6. try clear MU5 WM5 ST5 MI5.
    ablock HEAP7 PPIN' ACCQ7 OFFQ7. fz OFFQ7. clear ACCQ.
    pose proof (munch_refl [(spa, spa + 56)]%Z m7) as MU7. pose proof (wmono_refl ctasegs m7) as WM7.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.   (* [comment removed for export] *)
    pose proof MU7 as MU8. pose proof WM7 as WM8.
    match goal with H : mem_inv ctasegs m8 |- _ => rename H into MI8 end. match goal with H : rw_cells ctasegs m8 spa _ |- _ => rename H into FRL8 end.
    assert (ST8 : stk ctasegs m8 lo spa) by (first [assumption| eapply stk_transport; [exact ST7| exact MU8| exact WM8| cbn; clear; lia]]).
    assert (HEAP8 : @BnHeapA.AHEAP (push AR f 0) Σ2 OW LB' m8).
    { eapply (@AH_frame (push AR f 0)); [exact HEAP7| exact MU8| exact WM8|]. constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia| constructor]. }
    assert (SRC8 : bytes_at ctasegs m8 D src).
    { first [exact SRC7 | apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU8) in SRC7; [exact SRC7|]; rewrite SLEN, Z2Nat.id by lia; cbn; clear - DBC DH LEN CEIL LO SPAL; lia]. }
    thaw SEPD.
    apply evt_done.
    eapply (@asn1_ex_i2c_write_cpsA (push AR f 0) Q) with (lo := lo) (OW := OW) (LB := LB') (PVAL := PVAL) (PUT := f + 32) (A := A) (len := len) (D := D) (fl := fl)
      (C := P + der_hl len) (src := src) (bPV := bPV) (bPU := (q, f + 32, 4)) (bA := bA) (bC := bP) (bD := bD); rewrite ?ESPA; try reflexivity.
    + exact HEAP8.
    + exact ST8.
    + unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
    + unfold ASN1_EX_I2C_STACK_A, AEI_FRAME, RT_STACK. clear - LO SPAL. lia.
    + unfold USTACK_TOP. clear - TOP SPAH. lia.
    + clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
    + exact MI8.
    + exact FLEN1.
    + cbn [ar_RT push amb]. clear - CRED CR1 CR2. lia.
    + exact (INC _ PVIN).
    + exact PVL.
    + exact PVH.
    + clear - PVAL8. uchk_open. exact PVAL8.
    + exact HPV.
    + exact QIN.
    + clear - F8. uchk_open. Z.div_mod_to_equations. lia.
    + exact HPU.
    + exact (INC _ AIN).
    + exact AL.
    + unfold ASN1_STRING_SIZE. exact AH.
    + clear - A8. uchk_open. exact A8.
    + exact HS.
    + clear - LEN; lia.
    + exact FLR.
    + exact (INC _ PIN).
    + clear - PL HLR; lia.
    + exact PH.
    + exact (INC _ DIN).
    + exact DL.
    + exact DH.
    + exact SRC8.
    + exact SLEN.
    + clear - SEPD HLR LEN. lia.
    + (* [comment removed for export] *)
      fz SEPD.
      intros Σ3 m9 v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 v3 v4 v5 v6 F3 fc3 HEAP9 CR3 EL3 ST9 MI9 AG9 DST9.
      cbn [ar_RT push amb] in CR3, EL3. rewrite (ret_pc_even 0x2487d4) by (clear; lia).
      thaw SEPP.
      apply (rw_cells_agree _ _ _ _ _ AG9) in FRL8; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia| clear - Hxa PBC PH CEIL LO SPAL; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG9) in FRH; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia| clear - Hxa PBC PH CEIL LO SPAL SPAH; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG9) in HPP7; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists bPP; split; [exact (INC _ PPIN)| clear - Hxa PPL PPH; lia]| clear - Hxa SEPP HLR LEN; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG9) in HP17; [| intros xa Hxa; cbn [cells_size csize] in Hxa; rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia; split; [right; right; exists bP; split; [exact (INC _ PIN)| clear - Hxa PL PH HLR LEN; lia]| clear - Hxa; lia]].
      fz SEPP.
      clear ACCQ7. ablock HEAP9 PPIN' ACCQ9 OFFQ9. fz OFFQ9.
      pose proof (munch_refl [(spa, spa + 56); (PP, PP + 8)]%Z m9) as MU9. pose proof (wmono_refl ctasegs m9) as WM9.
      assert (OFFW9 : offshW [(spa, spa + 56); (PP, PP + 8)]%Z).
      { pose proof OFFQ as X. thaw X. cbn [offshW]. unfold SHLO, SHHI. clear - X CF1 CF2 CEIL LO SPAL PPL PPH. unfold SHLO, SHHI in X. lia. }
      apply cps_from_evt'.
      (* [comment removed for export] *)
      zstep. zstep. strue. zstep. zstep. zstep. thaw SEPP. zstep. fz SEPP. zstep.
      (* [comment removed for export] *)
      zstep. bnot. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
      match goal with H : munch _ m9 m10 |- _ => rename H into MU10 end. match goal with H : wmono ctasegs m9 m10 |- _ => rename H into WM10 end.
      match goal with H : mem_inv ctasegs m10 |- _ => rename H into MI10 end. match goal with H : rw_cells ctasegs m10 spa _ |- _ => rename H into FRL10 end.
      match goal with H : rw_cells ctasegs m10 PP _ |- _ => rename H into HPP10 end.
      assert (ST10 : stk ctasegs m10 lo spa) by (first [assumption| eapply stk_transport; [exact ST9| exact MU10| exact WM10| cbn; clear; lia]]).
      eapply evt_cut.
      { eapply ASN1_object_size_specA with (lo := lo) (len := len); rewrite ?ESPA; [exact ST10| exact MI10| clear - LO SPAL; lia| clear - LEN; lia| reflexivity| reflexivity| reflexivity]. }
      cbv beta. intros ms11 PO.
      destruct PO as (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m11 & -> & MU11 & WM11 & MI11 & ST11). rewrite ?ESPA in *.
      rewrite (ret_pc_even 0x248820) by (clear; lia).
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU11 WM11) in FRL10; [| cbn; clear; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU11 WM11) in FRH; [| cbn; clear - SPAH; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU11 WM11) in HPP10; [| cbn; clear - QBC PPH CEIL LO SPAL; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU11 WM11) in HP17; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; clear - PBC PH HLR LEN CEIL LO SPAL; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU11 WM11) in DST9; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; clear - PBC PH HLR LEN CEIL LO SPAL; lia].
      assert (MU911 : munch [(spa - 16, spa + 56); (PP, PP + 8)]%Z m9 m11).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU10]| eapply munch_weaken; [| exact MU11]]; unfold sub_fp; cbn [outside]; intros y Hy; clear - Hy; lia. }
      assert (WM911 : wmono ctasegs m9 m11) by (eapply wmono_trans; [exact WM10| exact WM11]).
      assert (HEAP11 : @BnHeapA.AHEAP (push AR f 0) Σ3 OW LB' m11).
      { eapply (@AH_frame (push AR f 0)); [exact HEAP9| exact MU911| exact WM911|]. constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia|].
        constructor; [right; right; exists bPP; split; [exact (INC _ PPIN)| cbn; clear - PPL PPH; lia]| constructor]. }
      (* [comment removed for export] *)
      zstep.
      apply evt_done. change (Z_to_bv 64 2394148) with (wz AIP_EXIT).
      eapply (@frame_obj_close (push AR f 0)) in HEAP11; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; clear; lia].
      eapply (@aip_epi_cps AR Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
        [exact HEAP11| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST11| exact CEIL| clear - LO SPAL; lia
        | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI11
        | exact (rw_cells_cb_first m11 spa _ 6 FRL10)| exact FRH| reflexivity|].
      intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
      thaw SEPP. thaw SEPD. thaw SEPA. thaw SEPV. thaw SEPVP. thaw SEPAP. thaw SEPDP. thaw G5.
      eapply K; [exact HEAP'| rewrite CR', CR3, CR2; clear - CR1; lia| rewrite LIVE', EL3, EL2; exact EL1| exact ST'| exact MI'| | | |].
      * (* [comment removed for export] *)
        assert (OUTW : forall a W, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> outside [(P, P + der_hl len + len); (PP, PP + 8)]%Z a ->
                  Forall (fun iv => (spa - 16 <= fst iv /\ snd iv <= spa + 56) \/ iv = (f + 32, f + 36) \/ iv = (P, P + der_hl len) \/ iv = (PP, PP + 8)) W ->
                  outside W a).
        { intros a W Ha Ho HW. induction W as [|[l' h'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW]. cbn [outside fst snd]. split; [| exact (IH HW)].
          cbn [outside fst snd] in Ho. cbn [fst snd] in H1.
          destruct H1 as [H1|[H1|[H1|H1]]]; [| injection H1 as -> ->| injection H1 as -> ->; clear - Ho HLR LEN; lia| injection H1 as -> ->; clear - Ho; lia].
          - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha H1 SPAH; lia| |].
            + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
              destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr H1 CEIL CE1 LO SPAL; lia.
            + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, B3'. clear - Hr H1 B3' CEIL LO SPAL. plia.
          - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEIL LO; lia| |].
            + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
              destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
            + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 0) with 64 in O.
              destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
        assert (LIFT : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LB') spa a).
        { intros a Ha. destruct Ha as [Ha1|[Ha1|(b & Hb & Hr)]]; [left; clear - Ha1 SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha1| right; right; exists b; split; [exact (INC b Hb)| exact Hr]]. }
        assert (FW1 : Forall (fun iv => (spa - 16 <= fst iv /\ snd iv <= spa + 56) \/ iv = (f + 32, f + 36) \/ iv = (P, P + der_hl len) \/ iv = (PP, PP + 8))
                        [(spa, spa + 56); (f + 32, f + 36)]%Z) by (constructor; [cbn [fst snd]; left; clear; lia| constructor; [cbn [fst snd]; right; left; reflexivity| constructor]]).
        assert (FW2 : Forall (fun iv => (spa - 16 <= fst iv /\ snd iv <= spa + 56) \/ iv = (f + 32, f + 36) \/ iv = (P, P + der_hl len) \/ iv = (PP, PP + 8))
                        [(spa - 16, spa + 56); (P, P + der_hl len); (PP, PP + 8)]%Z)
          by (constructor; [cbn [fst snd]; left; clear; lia| constructor; [cbn [fst snd]; right; right; left; reflexivity| constructor; [cbn [fst snd]; right; right; right; reflexivity| constructor]]]).
        assert (FW3 : Forall (fun iv => (spa - 16 <= fst iv /\ snd iv <= spa + 56) \/ iv = (f + 32, f + 36) \/ iv = (P, P + der_hl len) \/ iv = (PP, PP + 8))
                        [(spa, spa + 56)]%Z) by (constructor; [cbn [fst snd]; left; clear; lia| constructor]).
        assert (FW4 : Forall (fun iv => (spa - 16 <= fst iv /\ snd iv <= spa + 56) \/ iv = (f + 32, f + 36) \/ iv = (P, P + der_hl len) \/ iv = (PP, PP + 8))
                        [(spa - 16, spa + 56); (PP, PP + 8)]%Z) by (constructor; [cbn [fst snd]; left; clear; lia| constructor; [cbn [fst snd]; right; right; right; reflexivity| constructor]]).
        eapply agree_on_trans; [eapply agree_on_mono; [exact AGF| intros a [Ha _]; exact Ha]|].
        eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU4)| intros a [Ha Ho]; exact (OUTW a _ Ha Ho FW1)]|].
        eapply agree_on_trans; [eapply agree_on_mono; [exact AG5| intros a [Ha _]; exact (LIFT a Ha)]|].
        eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU57)| intros a [Ha Ho]; exact (OUTW a _ Ha Ho FW2)]|].
        eapply agree_on_trans; [eapply agree_on_mono; [exact AG9| intros a [Ha Ho]; split; [exact (LIFT a Ha)| cbn [outside fst snd] in Ho; clear - Ho HLR; lia]]|].
        eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU911)| intros a [Ha Ho]; exact (OUTW a _ Ha Ho FW4)]|].
        eapply agree_on_mono; [exact AG'|]. intros a [Ha _].
        destruct Ha as [Ha1|[Ha1|Ha1]]; [left; clear - Ha1 SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha1| right; right; exact Ha1].
      * eapply rw_cells_agree; [exact AG'| exact HPP10|]. intros xa Hxa. cbn in Hxa. right; right. exists bPP. split; [exact PPIN| clear - Hxa PPL PPH; lia].
      * exists hb. eapply rw_cells_agree; [exact AG'| exact HP17|]. intros xa Hxa. cbn [cells_size csize] in Hxa. rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia.
        right; right. exists bP. split; [exact PIN| clear - Hxa PL PH HLR LEN; lia].
      * eapply rw_cells_agree; [exact AG'| exact DST9|]. intros xa Hxa. cbn [cells_size csize] in Hxa. rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia.
        right; right. exists bP. split; [exact PIN| clear - Hxa PL PH HLR LEN; lia].
Qed.

End WithRT.
