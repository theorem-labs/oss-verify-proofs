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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA Fr_asn1_ex_i2c Fr_asn1_i2d_ex_primitive Fr_ASN1_item_ex_i2d W_asn1_enc_leavesA W_asn1_ex_i2cA W_asn1_i2d_primA.
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
Definition ASN1_ITEM_EX_I2D_STACK_A : Z := AIE_FRAME + ASN1_I2D_EX_PRIM_STACK_A.

(* [comment removed for export] *)
Lemma v_addiw0_small' : forall z, 0 <= z < 2^31 -> v_addiw (Z_to_bv 64 z) 0 = Z_to_bv 64 z.
Proof. intros z Hz. unfold v_addiw. f_equal. rewrite unsigned_lit by lia. rewrite Z.add_0_r. apply bk_swrap32_small. lia. Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma aie_body : forall (ra' gp t0' t1' t2' a2' a4' a5' a6' a7' s9 t3' t4' t5' t6' sp : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m3 : mem) (Σ1 : rts RT) (OW LB : list block) (lo f spa : Z) (g : nat) (junk : list byte)
    (j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 : list byte) (PVAL out : Z),
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m3 -> mem_inv ctasegs m3 -> stk ctasegs m3 lo spa -> ACEIL <= lo -> lo <= spa ->
  spa + 224 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP -> @fr_geo (push AR f 0) f 0 ->
  rw_cells ctasegs m3 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB g junk] ->
  0 <= PVAL < 2^64 -> 0 <= out < 2^64 ->
  evt ctasegs (fun ms' => exists (mb : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (wz PVAL) (wz out) (wz ITEM_OCTET_A) (Z_to_bv 64 (-1)) (wz 0) a5' a6' a7'
                   (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (wz ITEM_OCTET_A) (wz PVAL) (wz out) (Z_to_bv 64 f) s9 (wz 0) (Z_to_bv 64 (-1)) t3' t4' t5' t6')
               F' (Z_to_bv 64 0x247698) fc' None mb (seg_rom ctasegs)
      /\ munch [(spa + 112, spa + 120)]%Z m3 mb /\ wmono ctasegs m3 mb /\ mem_inv ctasegs mb
      /\ rw_cells ctasegs mb spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; C8 (Z_to_bv 64 f); CB g junk])
    (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa)
             (Z_to_bv 64 (ITEM_OCTET_A + 32)) (Z_to_bv 64 (Z.shiftr (ITEM_OCTET_A + 32) 3 + SHB)) a2' (Z_to_bv 64 (-13)) a4' a5' a6' a7'
             (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad f)) (wz ITEM_OCTET_A) (wz PVAL) (wz out) (Z_to_bv 64 f) s9 (wz 0) (Z_to_bv 64 (-1)) t3' t4' t5' t6')
        F' (wz AIE_BODY) fc' None m3 (seg_rom ctasegs)).
Proof.
  (* [comment removed for export] *)
  intros until out. intros HEAP3 MI3 ST3 CEIL LOSPA SPA224 TOP GEO FRL PVR OUTR.
  unfold AIE_BODY, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (CE1 & CE2 & CE3).
  assert (LO0 : 0 <= lo) by (destruct ST3 as [? _]; assumption).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
  pose proof (item_octA_of_heap _ _ _ _ _ HEAP3) as ((I1 & I2 & I3 & I4 & I5 & ACCI) & I7). unfold ITEM_OCTET_A in *.
  lit_addr I2. lit_addr I3. lit_addr I4. lit_addr I5. lit_addr I7.
  nrm.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CE3; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CE1 CEIL LO0 LOSPA SPA224 SPR; lia).
  pose proof (munch_refl [(spa + 112, spa + 120)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  assert (OFFW : offshW [(spa + 112, spa + 120)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - CE1 CE2 CEIL LOSPA; lia).
  fz G5.
  (* [comment removed for export] *)
  ab_shload 1. rewrite ?zxb_z8, ?sxb_z8. step. step. first [if_false | if_true].
  (* [comment removed for export] *)
  zstep. zstep. ab_shload 1. rewrite ?zxb_z8, ?sxb_z8. step. step. first [if_false | if_true].
  zstep. zstep. btaken. zstep. zstep. btaken. zstep. zstep. zstep. zstep. zstep.
  rewrite ?zxb_z8.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply evt_done; cbv beta; exists mx end. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  lazymatch goal with |- rw_cells _ ?mx _ _ => match goal with H : rw_cells ctasegs mx spa _ |- _ => exact H end end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aie_len_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (PVAL A len D fl : Z) (bPV bA : block),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + ASN1_ITEM_EX_I2D_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> fr_depth_ok 3%nat -> 3 <= rt_credit RT Σ ->
  In bPV (OW ++ LB) -> blk_addr bPV <= PVAL -> PVAL + 8 <= blk_addr bPV + blk_size bPV -> PVAL mod 8 = 0 -> rw_cells ctasegs m PVAL [C8 (wz A)] ->
  In bA (OW ++ LB) -> blk_addr bA <= A -> A + ASN1_STRING_SIZE <= blk_addr bA + blk_size bA -> A mod 8 = 0 ->
  rw_cells ctasegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  0 <= len < 65536 -> 0 <= D < 2^64 -> 0 <= fl < 2^64 ->
  a0 = wz PVAL -> a1 = wz 0 -> a2 = wz ITEM_OCTET_A -> a3 = Z_to_bv 64 (-1) -> a4 = wz 0 ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 3 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m' ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 (der_hl len + len)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_ITEM_EX_I2D_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until bA. intros HEAP ST CEIL LO TOP AL16 MI -> FD CRED PVIN PVL PVH PVAL8 HPV AIN AL AH A8 HS LEN DR FLR -> -> -> -> -> K.
  unfold ASN1_ITEM_EX_I2D_STACK_A, ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AIE_FRAME, AIP_FRAME, AEI_FRAME in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (der_hl_range len LEN) as HLR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PVIN) as (VB0 & _ & _ & VBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP AIN) as (AB0 & _ & _ & ABC & _). cbn [blk_addr blk_size fst snd] in *. nrm.
  destruct (fr_depth_push 2%nat 0 0%nat FD) as [FLEN _].
  change (wz ASN1_ITEM_EX_I2D_A) with (wz AIE_ENTRY).
  eapply (aie_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold AIE_FRAME, RT_STACK; clear - LO; lia| exact TOP| exact AL16| vm_compute; congruence (* [comment removed for export] *)| vm_compute; reflexivity (* [comment removed for export] *)| exact MI| reflexivity| exact FLEN| clear - CRED; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 jf24 jf32 jf36
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold MallocRep.wz. rewrite !(unsigned_lit ITEM_OCTET_A) by (unfold ITEM_OCTET_A; clear; lia).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
  destruct (fr_depth_push 2%nat f 0%nat FD) as [_ FD1].
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (CF1 & CF2 & CF3). nrm.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEIL LO0 LO SPAL SPAH SPR; lia).
  pose proof (FRESH _ PVIN) as OFV. pose proof (FRESH _ AIN) as OFA. unfold off_fr in OFV, OFA. change (fs_size 0) with 64 in OFV, OFA.
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPV; [| intros xa Hxa; right; right; exists bPV; split; [exact PVIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HS; [| intros xa Hxa; right; right; exists bA; split; [exact AIN| unfold asn1_string_cells, ASN1_STRING_SIZE in *; cbn in Hxa; lia]].
  apply cps_from_evt'. eapply evt_cut.
  { eapply (aie_body ra' gp t0' t1' t2' a2' a4' a5' a6' a7' s9 t3' t4' t5' t6' sp F1 fc1 m3 Σ1 OW LB lo f spa g junk j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 PVAL 0);
      try eassumption; try reflexivity.
    - clear - LO SPAL. lia.
    - clear - SPAH. lia.
    - clear - VB0 VBC PVL PVH CE3. lia.
    - clear. lia. }
  cbv beta. intros msb (mb & -> & MUb & WMb & MIb & FRLb). unfold MallocRep.wz.
  assert (STb : stk ctasegs mb lo spa) by (eapply stk_transport; [exact ST3| exact MUb| exact WMb| cbn; clear; lia]).
  assert (HEAPb : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB mb).
  { eapply (@AH_frame (push AR f 0)); [exact HEAP3| exact MUb| exact WMb|]. constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia| constructor]. }
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in FRH; [| cbn; clear - SPAH; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in HPV; [| cbn; clear - VBC PVH CEIL LO SPAL; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in HS; [| unfold asn1_string_cells; cbn; clear - ABC AH CEIL LO SPAL; unfold ASN1_STRING_SIZE in AH; lia].
  (* [comment removed for export] *)
  zstep. apply evt_done.
  eapply (@aip_len_cpsA (push AR f 0) Q) with (lo := lo) (OW := OW) (LB := LB) (PVAL := PVAL) (A := A) (len := len) (D := D) (fl := fl) (bPV := bPV) (bA := bA);
    rewrite ?ESPA; try reflexivity.
  - exact HEAPb.
  - exact STb.
  - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
  - unfold ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AIP_FRAME, AEI_FRAME, RT_STACK. clear - LO SPAL. lia.
  - unfold USTACK_TOP. clear - TOP SPAH. lia.
  - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
  - exact MIb.
  - exact FD1.
  - cbn [ar_RT push amb]. clear - CRED CR1. lia.
  - exact PVIN.
  - exact PVL.
  - exact PVH.
  - clear - PVAL8. uchk_open. exact PVAL8.
  - exact HPV.
  - exact AIN.
  - exact AL.
  - exact AH.
  - clear - A8. uchk_open. exact A8.
  - exact HS.
  - exact LEN.
  - exact DR.
  - exact FLR.
  - intros Σ2 m5 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 HEAP5 CR2 EL2 ST5 MI5 AG5.
    cbn [ar_RT push amb] in CR2, EL2. rewrite (ret_pc_even 0x24769c) by (clear; lia).
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRLb; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRH; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia].
    pose proof (munch_refl (@nil (Z * Z)) m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply evt_done. change (Z_to_bv 64 2390616) with (wz AIE_EXIT).
    eapply (@aie_epi_cps AR Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAP5| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST5| exact CEIL| clear - LO SPAL; lia
      | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI5
      | exact (rw_cells_cb_first m5 spa _ 14 FRLb)| exact FRH| reflexivity|].
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'. rewrite (v_addiw0_small' (der_hl len + len)) by (clear - LEN HLR; lia).
    eapply K; [exact HEAP'| rewrite CR', CR2; clear - CR1; lia| rewrite LIVE', EL2; exact EL1| exact ST'| exact MI'|].
    eapply agree_on_trans; [exact AGF|].
    eapply agree_on_trans.
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUb)|]. intros a Ha. cbn [outside fst snd]. split; [| exact I].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL CE1 LO SPAL; lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, B3'. clear - Hr B3' CEIL LO SPAL. plia. }
    eapply agree_on_trans.
    { eapply agree_on_mono; [exact AG5|]. intros a Ha.
      destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha]. }
    eapply agree_on_mono; [exact AG'|]. intros a Ha.
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aie_write_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (PVAL A len D fl PP P : Z) (src j1 j2 : list byte) (bPV bA bPP bP bD : block),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + ASN1_ITEM_EX_I2D_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> fr_depth_ok 3%nat -> 4 <= rt_credit RT Σ ->
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
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 4 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(P, P + der_hl len + len); (PP, PP + 8)]%Z a) m m' ->
     rw_cells ctasegs m' PP [C8 (wz (P + der_hl len + len))] ->
     (exists hb, rw_cells ctasegs m' P [CB (Z.to_nat (der_hl len)) hb]) -> rw_cells ctasegs m' (P + der_hl len) [CB (Z.to_nat len) src] ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 (der_hl len + len)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_ITEM_EX_I2D_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until bD. intros HEAP ST CEIL LO TOP AL16 MI -> FD CRED PVIN PVL PVH PVAL8 HPV AIN AL AH A8 HS LEN FLR
         PPIN PPL PPH PP8 HPP PIN PL PH HP1 HP2 DIN DL DH SRC SLEN SEPP SEPD SEPA SEPV SEPVP SEPAP SEPDP -> -> -> -> -> K.
  unfold ASN1_ITEM_EX_I2D_STACK_A, ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AIE_FRAME, AIP_FRAME, AEI_FRAME in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (der_hl_range len ltac:(clear - LEN; lia)) as HLR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PVIN) as (VB0 & _ & _ & VBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP AIN) as (AB0 & _ & _ & ABC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PPIN) as (QB0 & _ & _ & QBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PIN) as (PB0 & _ & _ & PBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP DIN) as (DB0 & _ & _ & DBC & _). cbn [blk_addr blk_size fst snd] in *. nrm.
  fz SEPP. fz SEPD. fz SEPA. fz SEPV. fz SEPVP. fz SEPAP. fz SEPDP.
  destruct (fr_depth_push 2%nat 0 0%nat FD) as [FLEN _].
  change (wz ASN1_ITEM_EX_I2D_A) with (wz AIE_ENTRY).
  eapply (aie_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold AIE_FRAME, RT_STACK; clear - LO; lia| exact TOP| exact AL16| vm_compute; congruence (* [comment removed for export] *)| vm_compute; reflexivity (* [comment removed for export] *)| exact MI| reflexivity| exact FLEN| clear - CRED; lia|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 jf24 jf32 jf36
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold MallocRep.wz. rewrite !(unsigned_lit ITEM_OCTET_A) by (unfold ITEM_OCTET_A; clear; lia).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
  destruct (fr_depth_push 2%nat f 0%nat FD) as [_ FD1].
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (CF1 & CF2 & CF3). nrm.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEIL LO0 LO SPAL SPAH SPR; lia).
  pose proof (FRESH _ PVIN) as OFV. pose proof (FRESH _ AIN) as OFA. pose proof (FRESH _ PPIN) as OFQ. pose proof (FRESH _ PIN) as OFP. pose proof (FRESH _ DIN) as OFD.
  unfold off_fr in OFV, OFA, OFQ, OFP, OFD. change (fs_size 0) with 64 in OFV, OFA, OFQ, OFP, OFD.
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPV; [| intros xa Hxa; right; right; exists bPV; split; [exact PVIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HS; [| intros xa Hxa; right; right; exists bA; split; [exact AIN| unfold asn1_string_cells, ASN1_STRING_SIZE in *; cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPP; [| intros xa Hxa; right; right; exists bPP; split; [exact PPIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HP1; [| intros xa Hxa; right; right; exists bP; split; [exact PIN| cbn [cells_size csize] in Hxa; rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HP2; [| intros xa Hxa; right; right; exists bP; split; [exact PIN| cbn [cells_size csize] in Hxa; rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia; lia]].
  apply (bytes_at_agree _ m m3 _ _ AGF) in SRC; [| intros xa Hxa; rewrite SLEN, Z2Nat.id in Hxa by lia; right; right; exists bD; split; [exact DIN| lia]].
  apply cps_from_evt'. eapply evt_cut.
  { eapply (aie_body ra' gp t0' t1' t2' a2' a4' a5' a6' a7' s9 t3' t4' t5' t6' sp F1 fc1 m3 Σ1 OW LB lo f spa g junk j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 PVAL PP);
      try eassumption; try reflexivity.
    - clear - LO SPAL. lia.
    - clear - SPAH. lia.
    - clear - VB0 VBC PVL PVH CE3. lia.
    - clear - QB0 QBC PPL PPH CE3. lia. }
  cbv beta. intros msb (mb & -> & MUb & WMb & MIb & FRLb). unfold MallocRep.wz.
  assert (STb : stk ctasegs mb lo spa) by (eapply stk_transport; [exact ST3| exact MUb| exact WMb| cbn; clear; lia]).
  assert (HEAPb : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB mb).
  { eapply (@AH_frame (push AR f 0)); [exact HEAP3| exact MUb| exact WMb|]. constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia| constructor]. }
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in FRH; [| cbn; clear - SPAH; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in HPV; [| cbn; clear - VBC PVH CEIL LO SPAL; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in HS; [| unfold asn1_string_cells; cbn; clear - ABC AH CEIL LO SPAL; unfold ASN1_STRING_SIZE in AH; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in HPP; [| cbn; clear - QBC PPH CEIL LO SPAL; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in HP1; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; clear - PBC PH HLR LEN CEIL LO SPAL; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in HP2; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; clear - PBC PH HLR LEN CEIL LO SPAL; lia].
  apply (fun H => bytes_at_transport _ _ _ _ _ _ H MUb) in SRC; [| rewrite SLEN, Z2Nat.id by lia; cbn; clear - DBC DH LEN CEIL LO SPAL; lia].
  thaw SEPP. thaw SEPD. thaw SEPA. thaw SEPV. thaw SEPVP. thaw SEPAP. thaw SEPDP.
  (* [comment removed for export] *)
  zstep. apply evt_done.
  eapply (@aip_write_cpsA (push AR f 0) Q) with (lo := lo) (OW := OW) (LB := LB) (PVAL := PVAL) (A := A) (len := len) (D := D) (fl := fl) (PP := PP) (P := P)
    (src := src) (j1 := j1) (j2 := j2) (bPV := bPV) (bA := bA) (bPP := bPP) (bP := bP) (bD := bD);
    rewrite ?ESPA; try reflexivity.
  - exact HEAPb.
  - exact STb.
  - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
  - unfold ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AIP_FRAME, AEI_FRAME, RT_STACK. clear - LO SPAL. lia.
  - unfold USTACK_TOP. clear - TOP SPAH. lia.
  - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
  - exact MIb.
  - exact FD1.
  - cbn [ar_RT push amb]. clear - CRED CR1. lia.
  - exact PVIN.
  - exact PVL.
  - exact PVH.
  - clear - PVAL8. uchk_open. exact PVAL8.
  - exact HPV.
  - exact AIN.
  - exact AL.
  - exact AH.
  - clear - A8. uchk_open. exact A8.
  - exact HS.
  - exact LEN.
  - exact FLR.
  - exact PPIN.
  - exact PPL.
  - exact PPH.
  - clear - PP8. uchk_open. exact PP8.
  - exact HPP.
  - exact PIN.
  - exact PL.
  - exact PH.
  - exact HP1.
  - exact HP2.
  - exact DIN.
  - exact DL.
  - exact DH.
  - exact SRC.
  - exact SLEN.
  - exact SEPP.
  - exact SEPD.
  - exact SEPA.
  - exact SEPV.
  - exact SEPVP.
  - exact SEPAP.
  - exact SEPDP.
  - intros Σ2 m5 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 HEAP5 CR2 EL2 ST5 MI5 AG5 HPP5 HP15 HP25.
    cbn [ar_RT push amb] in CR2, EL2. rewrite (ret_pc_even 0x24769c) by (clear; lia).
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRLb; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia| cbn [outside fst snd]; clear - Hxa PBC PH QBC PPH CEIL LO SPAL; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRH; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia| cbn [outside fst snd]; clear - Hxa PBC PH QBC PPH CEIL LO SPAL SPAH; lia]].
    pose proof (munch_refl (@nil (Z * Z)) m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    apply evt_done. change (Z_to_bv 64 2390616) with (wz AIE_EXIT).
    eapply (@aie_epi_cps AR Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAP5| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST5| exact CEIL| clear - LO SPAL; lia
      | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI5
      | exact (rw_cells_cb_first m5 spa _ 14 FRLb)| exact FRH| reflexivity|].
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'. rewrite (v_addiw0_small' (der_hl len + len)) by (clear - LEN HLR; lia).
    eapply K; [exact HEAP'| rewrite CR', CR2; clear - CR1; lia| rewrite LIVE', EL2; exact EL1| exact ST'| exact MI'| | | |].
    2:{ eapply rw_cells_agree; [exact AG'| exact HPP5|]. intros xa Hxa. cbn in Hxa. right; right. exists bPP. split; [exact PPIN| clear - Hxa PPL PPH; lia]. }
    2:{ destruct HP15 as [hb HP15]. exists hb. eapply rw_cells_agree; [exact AG'| exact HP15|]. intros xa Hxa. cbn [cells_size csize] in Hxa. rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia.
        right; right. exists bP. split; [exact PIN| clear - Hxa PL PH HLR LEN; lia]. }
    2:{ eapply rw_cells_agree; [exact AG'| exact HP25|]. intros xa Hxa. cbn [cells_size csize] in Hxa. rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia.
        right; right. exists bP. split; [exact PIN| clear - Hxa PL PH HLR LEN; lia]. }
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF| intros a [Ha _]; exact Ha]|].
    eapply agree_on_trans.
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUb)|]. intros a [Ha _]. cbn [outside fst snd]. split; [| exact I].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL CE1 LO SPAL; lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, B3'. clear - Hr B3' CEIL LO SPAL. plia. }
    eapply agree_on_trans.
    { eapply agree_on_mono; [exact AG5|]. intros a [Ha Ho]. split; [| exact Ho].
      destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha]. }
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _].
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
Qed.

End WithRT.
