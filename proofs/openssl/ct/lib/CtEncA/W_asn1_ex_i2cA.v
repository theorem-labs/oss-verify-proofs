(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes ApBase ApPrim.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA Fr_asn1_ex_i2c.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
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

(* [comment removed for export] *)
Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
(* [comment removed for export] *)
Ltac ab_ichk t u J :=
  first [ match goal with OK : absh_ok _ _ _ |- _ => ab_join t u J OK end
        | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true] ].
(* [comment removed for export] *)
Ltac lit_addr H := lazymatch type of H with
  | ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H
  | rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H end.
(* [comment removed for export] *)
Ltac fz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Ltac thaw H := unfold frozen in H.

(* [comment removed for export] *)
Definition ASN1_EX_I2C_STACK_A : Z := AEI_FRAME + RT_STACK.
Definition AEI_COUT : Z := 0x248de0.        (* [comment removed for export] *)
Definition AEI_JT5 : Z := 0x733a4.          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac rom_cell4 A v :=
  intros m MI;
  let bs := eval vm_compute in (match image_bytes ctasegs A 4 with Some bs => bs | None => [] end) in
  apply (ro_cells_recastA m A [CB 4 bs] [C4 (Z_to_bv 64 v)]);
  [ apply (ro_cells_image ctasegs m A bs MI); [vm_compute; reflexivity| lia| cbn; lia]
  | cbn; repeat split; reflexivity
  | cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]] ].

(* [comment removed for export] *)
Lemma jt_ex_i2c_octA : forall m, mem_inv ctasegs m -> ro_cells ctasegs m AEI_JT5 [C4 (Z_to_bv 64 1923364)].
Proof. unfold AEI_JT5. rom_cell4 0x733a4 1923364. Qed.

(* [comment removed for export] *)
Lemma v_addiw0_small : forall z, 0 <= z < 2^31 -> v_addiw (Z_to_bv 64 z) 0 = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_addiw. f_equal. rewrite unsigned_lit by lia. rewrite Z.add_0_r. apply bk_swrap32_small. lia.
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
Definition item_octA (m : mem) : Prop := item_cellsA m ITEM_OCTET_A V_ASN1_OCTET_STRING /\ ro_cells ctasegs m (ITEM_OCTET_A + 40) [C8 (Z_to_bv 64 0)].

Lemma item_octA_of_heap : forall (AR' : ARun) Σ OW LB m, @BnHeapA.AHEAP AR' Σ OW LB m -> item_octA m.
Proof.
  intros AR' Σ OW LB m H. split; [exact (@item_cellsA_octet AR' Σ OW LB m H)|].
  pose proof (af_relro _ (@ar_AF AR') Σ m (@AH_art AR' _ _ _ _ H)) as R. unfold ITEM_OCTET_A.
  apply (relro_ro_cells m (0x547620 + 40) [C8 (Z_to_bv 64 0)]); [exact R| cbn; auto| unfold RELRO_LO; lia| unfold RELRO_HI; cbn; lia| vm_compute; reflexivity].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aei_body : forall (ra' gp t0' t1' t2' a2' a4' a5' a6' a7' s10 s11 t3' t4' t5' t6' sp : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m3 : mem) (Σ1 : rts RT) (OW LB : list block) (lo f spa : Z) (g : nat) (junk j0 : list byte)
    (PVAL PUT A len D fl cout : Z) (bPV bPU bA : block),
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3 -> mem_inv ctasegs m3 -> stk ctasegs m3 lo spa -> ACEIL <= lo -> lo <= spa ->
  spa + 96 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP -> @fr_geo (push AR f 1) f 1 ->
  rw_cells ctasegs m3 spa [CB 8 j0; CB g junk] ->
  In bPV (OW ++ LB) -> blk_addr bPV <= PVAL -> PVAL + 8 <= blk_addr bPV + blk_size bPV -> PVAL mod 8 = 0 -> rw_cells ctasegs m3 PVAL [C8 (wz A)] ->
  In bPU (OW ++ LB) -> blk_addr bPU <= PUT -> PUT + 4 <= blk_addr bPU + blk_size bPU -> PUT mod 8 = 0 -> rw_cells ctasegs m3 PUT [C4 (wz V_ASN1_OCTET_STRING)] ->
  In bA (OW ++ LB) -> blk_addr bA <= A -> A + ASN1_STRING_SIZE <= blk_addr bA + blk_size bA -> A mod 8 = 0 ->
  rw_cells ctasegs m3 A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  0 <= len < 2^31 -> 0 <= D < 2^64 -> 0 <= fl < 2^64 -> 0 <= cout < 2^64 ->
  evt ctasegs (fun ms' => exists (x10 x13 x14 : word) (mb : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) x10 (wz D) (wz A) x13 x14 a5' a6' a7'
                   (Z_to_bv 64 f) (wz cout) (Z_to_bv 64 len) (wz PVAL) (wz PUT) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) s10 s11 t3' t4' t5' t6')
               F' (Z_to_bv 64 AEI_COUT) fc' None mb (seg_rom ctasegs)
      /\ munch [(spa, spa + 8)]%Z m3 mb /\ wmono ctasegs m3 mb /\ mem_inv ctasegs mb
      /\ rw_cells ctasegs mb spa [C8 (Z_to_bv 64 f); CB g junk])
    (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa)
             (Z_to_bv 64 (ITEM_OCTET_A + 32)) (Z_to_bv 64 (Z.shiftr (ITEM_OCTET_A + 32) 3 + SHB)) a2' (Z_to_bv 64 (-14)) a4' a5' a6' a7'
             (Z_to_bv 64 f) (wz cout) (wz ITEM_OCTET_A) (wz PVAL) (wz PUT) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) s10 s11 t3' t4' t5' t6')
        F' (wz AEI_BODY) fc' None m3 (seg_rom ctasegs)).
Proof.
  (* [comment removed for export] *)
  intros until bA. intros HEAP3 MI3 ST3 CEIL LOSPA SPA96 TOP GEO FRL PVIN PVL PVH PVAL8 HPV PUIN PUL PUH PUT8 HPU AIN AL AH A8 HS LEN DR FLR CR.
  unfold AEI_BODY, AEI_COUT, V_ASN1_OCTET_STRING, ASN1_STRING_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (@AH_ceil (push AR f 1) _ _ _ _ HEAP3) as (CE1 & CE2 & CE3).
  assert (LO0 : 0 <= lo) by (destruct ST3 as [? _]; assumption).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G4, G5.
  (* [comment removed for export] *)
  pose proof (@AH_range_gen (push AR f 1) _ _ _ _ _ HEAP3 PVIN) as (VB0 & _ & _ & VBC & VBI).
  pose proof (@AH_range_gen (push AR f 1) _ _ _ _ _ HEAP3 PUIN) as (UB0 & _ & _ & UBC & UBI).
  pose proof (@AH_range_gen (push AR f 1) _ _ _ _ _ HEAP3 AIN) as (AB0 & _ & _ & ABC & ABI).
  ablock HEAP3 PVIN ACCV OFFV. ablock HEAP3 PUIN ACCU OFFU. ablock HEAP3 AIN ACCA OFFA.
  cbn [blk_addr blk_size fst snd] in *.
  (* [comment removed for export] *)
  unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *. cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CE3; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CE1 CEIL LO0 LOSPA SPA96 SPR; lia).
  (* [comment removed for export] *)
  pose proof (item_octA_of_heap _ _ _ _ _ HEAP3) as ((I1 & I2 & I3 & I4 & I5 & ACCI) & I7). unfold ITEM_OCTET_A in *.
  lit_addr I2. lit_addr I3. lit_addr I4. lit_addr I5. lit_addr I7.
  pose proof (jt_ex_i2c_octA m3 MI3) as JT. unfold AEI_JT5 in JT.
  unfold asn1_string_cells, MallocRep.wz in HS.
  pose proof (munch_refl [(spa, spa + 8)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  assert (OFFW : offshW [(spa, spa + 8)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - CE1 CE2 CEIL LOSPA; lia).
  (* [comment removed for export] *)
  fz VBI. fz UBI. fz ABI. fz OFFV. fz OFFU. fz OFFA.
  (* [comment removed for export] *)
  ab_shload 8. rewrite ?zxb_z8. step. step. first [if_false | if_true]. zstep. zstep. btaken.
  (* [comment removed for export] *)
  zstep. zstep. btaken.
  (* [comment removed for export] *)
  zstep. zstep. zstep. bnot.
  (* [comment removed for export] *)
  zstep. zstep. sfalse. zstep. zstep. zstep. btaken.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. bnot.
  (* [comment removed for export] *)
  do 8 zstep.
  (* [comment removed for export] *)
  do 5 zstep. btaken.
  (* [comment removed for export] *)
  do 2 zstep. ab_shload 4. rewrite ?zxb_z8, ?sxb_z8. step. step. first [if_false | if_true].
  (* [comment removed for export] *)
  do 2 zstep. rewrite (sx32_small len) by lia.
  apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  lazymatch goal with |- rw_cells _ ?mx _ _ => match goal with H : rw_cells ctasegs mx spa _ |- _ => exact H end end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asn1_ex_i2c_len_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (PVAL PUT A len D fl : Z) (bPV bPU bA : block),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + ASN1_EX_I2C_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FRM < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  In bPV (OW ++ LB) -> blk_addr bPV <= PVAL -> PVAL + 8 <= blk_addr bPV + blk_size bPV -> PVAL mod 8 = 0 -> rw_cells ctasegs m PVAL [C8 (wz A)] ->
  In bPU (OW ++ LB) -> blk_addr bPU <= PUT -> PUT + 4 <= blk_addr bPU + blk_size bPU -> PUT mod 8 = 0 -> rw_cells ctasegs m PUT [C4 (wz V_ASN1_OCTET_STRING)] ->
  In bA (OW ++ LB) -> blk_addr bA <= A -> A + ASN1_STRING_SIZE <= blk_addr bA + blk_size bA -> A mod 8 = 0 ->
  rw_cells ctasegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  0 <= len < 2^31 -> 0 <= D < 2^64 -> 0 <= fl < 2^64 ->
  a0 = wz PVAL -> a1 = wz 0 -> a2 = wz PUT -> a3 = wz ITEM_OCTET_A ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 1 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m' ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_EX_I2C_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until bA. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED PVIN PVL PVH PVAL8 HPV PUIN PUL PUH PUT8 HPU AIN AL AH A8 HS LEN DR FLR -> -> -> -> K.
  unfold ASN1_EX_I2C_STACK_A, AEI_FRAME in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PVIN) as (VB0 & _ & _ & VBC & _). pose proof (AH_range_gen _ _ _ _ _ HEAP PUIN) as (UB0 & _ & _ & UBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP AIN) as (AB0 & _ & _ & ABC & _). cbn [blk_addr blk_size fst snd] in *. nrm.
  change (wz ASN1_EX_I2C_A) with (wz AEI_ENTRY).
  eapply (aei_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold AEI_FRAME, RT_STACK; clear - LO; lia| exact TOP| exact AL16| vm_compute; reflexivity (* [comment removed for export] *)| exact MI| reflexivity| exact FLEN| exact CRED|].
  intros Σ1 m3 f spa g junk gj j0 ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 jf24 jf40 jf64 jf65 jst
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold MallocRep.wz. rewrite !(unsigned_lit ITEM_OCTET_A) by (unfold ITEM_OCTET_A; clear; lia).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G4, G5. nrm.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPV; [| intros xa Hxa; right; right; exists bPV; split; [exact PVIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPU; [| intros xa Hxa; right; right; exists bPU; split; [exact PUIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HS; [| intros xa Hxa; right; right; exists bA; split; [exact AIN| unfold asn1_string_cells, ASN1_STRING_SIZE in *; cbn in Hxa; lia]].
  apply cps_from_evt'. eapply evt_cut.
  { eapply (aei_body ra' gp t0' t1' t2' a2' a4' a5' a6' a7' s10 s11 t3' t4' t5' t6' sp F1 fc1 m3 Σ1 OW LB lo f spa g junk j0 PVAL PUT A len D fl 0 bPV bPU bA);
      try eassumption; try reflexivity.
    - clear - LO SPAL. lia.
    - clear - SPAH. lia.
    - clear. lia. }
  cbv beta. intros msb (x10 & x13 & x14 & mb & -> & MUb & WMb & MIb & FRLb). unfold AEI_COUT, MallocRep.wz.
  assert (STb : stk ctasegs mb lo spa) by (eapply stk_transport; [exact ST3| exact MUb| exact WMb| cbn; clear; lia]).
  assert (HEAPb : @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB mb).
  { eapply (@AH_frame (push AR f 1)); [exact HEAP3| exact MUb| exact WMb|]. constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia| constructor]. }
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in FRH; [| cbn; clear - SPAH; lia].
  (* [comment removed for export] *)
  zstep. btaken. zstep. zstep.
  apply evt_done. change (Z_to_bv 64 2395680) with (wz AEI_EXIT).
  eapply (aei_epi_cps Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAPb| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STb| exact CEIL| clear - LO SPAL; lia
    | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIb
    | exact FRLb| exact FRH| reflexivity|].
  intros Σ' m' x11' HEAP' CR' LIVE' ST' MI' AG'. rewrite (v_addiw0_small len) by (clear - LEN; lia).
  eapply K; [exact HEAP'| rewrite CR'; exact CR1| rewrite LIVE'; exact EL1| exact ST'| exact MI'|].
  (* [comment removed for export] *)
  eapply agree_on_trans; [exact AGF|].
  eapply agree_on_trans.
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUb)|]. intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH; lia| |].
    - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL CE1 LO SPAL; plia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEIL LO SPAL. plia. }
  eapply agree_on_mono; [exact AG'|]. intros a Ha.
  destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asn1_ex_i2c_write_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z)
    (PVAL PUT A len D fl C : Z) (src : list byte) (bPV bPU bA bC bD : block),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + ASN1_EX_I2C_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FRM < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  In bPV (OW ++ LB) -> blk_addr bPV <= PVAL -> PVAL + 8 <= blk_addr bPV + blk_size bPV -> PVAL mod 8 = 0 -> rw_cells ctasegs m PVAL [C8 (wz A)] ->
  In bPU (OW ++ LB) -> blk_addr bPU <= PUT -> PUT + 4 <= blk_addr bPU + blk_size bPU -> PUT mod 8 = 0 -> rw_cells ctasegs m PUT [C4 (wz V_ASN1_OCTET_STRING)] ->
  In bA (OW ++ LB) -> blk_addr bA <= A -> A + ASN1_STRING_SIZE <= blk_addr bA + blk_size bA -> A mod 8 = 0 ->
  rw_cells ctasegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  0 < len < 2^31 -> 0 <= fl < 2^64 ->
  In bC (OW ++ LB) -> blk_addr bC <= C -> C + len <= blk_addr bC + blk_size bC ->
  In bD (OW ++ LB) -> blk_addr bD <= D -> D + len <= blk_addr bD + blk_size bD ->
  bytes_at ctasegs m D src -> length src = Z.to_nat len -> (C + len <= D \/ D + len <= C) ->
  a0 = wz PVAL -> a1 = wz C -> a2 = wz PUT -> a3 = wz ITEM_OCTET_A ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 1 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (C <= a < C + len)) m m' ->
     rw_cells ctasegs m' C [CB (Z.to_nat len) src] ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_EX_I2C_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until bD. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED PVIN PVL PVH PVAL8 HPV PUIN PUL PUH PUT8 HPU AIN AL AH A8 HS LEN FLR
         CIN CL CH DIN DL DH SRC SLEN SEP -> -> -> -> K.
  unfold ASN1_EX_I2C_STACK_A, AEI_FRAME in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PVIN) as (VB0 & _ & _ & VBC & _). pose proof (AH_range_gen _ _ _ _ _ HEAP PUIN) as (UB0 & _ & _ & UBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP AIN) as (AB0 & _ & _ & ABC & _). pose proof (AH_range_gen _ _ _ _ _ HEAP CIN) as (CB0 & _ & _ & CBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP DIN) as (DB0 & _ & _ & DBC & _). cbn [blk_addr blk_size fst snd] in *. nrm.
  assert (DR : 0 <= D < 2^64) by (clear - DB0 DL DH DBC CE3 LEN; lia).
  change (frozen (C + len <= D \/ D + len <= C)) in SEP.
  change (wz ASN1_EX_I2C_A) with (wz AEI_ENTRY).
  eapply (aei_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold AEI_FRAME, RT_STACK; clear - LO; lia| exact TOP| exact AL16| vm_compute; reflexivity (* [comment removed for export] *)| exact MI| reflexivity| exact FLEN| exact CRED|].
  intros Σ1 m3 f spa g junk gj j0 ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 jf24 jf40 jf64 jf65 jst
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold MallocRep.wz. rewrite !(unsigned_lit ITEM_OCTET_A) by (unfold ITEM_OCTET_A; clear; lia).
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G4, G5. nrm.
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPV; [| intros xa Hxa; right; right; exists bPV; split; [exact PVIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HPU; [| intros xa Hxa; right; right; exists bPU; split; [exact PUIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in HS; [| intros xa Hxa; right; right; exists bA; split; [exact AIN| unfold asn1_string_cells, ASN1_STRING_SIZE in *; cbn in Hxa; lia]].
  apply (bytes_at_agree _ m m3 _ _ AGF) in SRC; [| intros xa Hxa; rewrite SLEN, Z2Nat.id in Hxa by lia; right; right; exists bD; split; [exact DIN| lia]].
  apply cps_from_evt'. eapply evt_cut.
  { eapply (aei_body ra' gp t0' t1' t2' a2' a4' a5' a6' a7' s10 s11 t3' t4' t5' t6' sp F1 fc1 m3 Σ1 OW LB lo f spa g junk j0 PVAL PUT A len D fl C bPV bPU bA);
      try eassumption; try reflexivity.
    - clear - LO SPAL. lia.
    - clear - SPAH. lia.
    - clear - LEN. lia.
    - clear - CB0 CL CH CBC CE3 LEN. lia. }
  cbv beta. intros msb (x10 & x13 & x14 & mb & -> & MUb & WMb & MIb & FRLb). unfold AEI_COUT, MallocRep.wz.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEIL LO SPAL SPAH SPR ST; destruct ST as [? _]; lia).
  assert (STb : stk ctasegs mb lo spa) by (eapply stk_transport; [exact ST3| exact MUb| exact WMb| cbn; clear; lia]).
  assert (HEAPb : @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB mb).
  { eapply (@AH_frame (push AR f 1)); [exact HEAP3| exact MUb| exact WMb|]. constructor; [left; cbn [fst snd]; clear - CEIL LO SPAL SPAH TOP; plia| constructor]. }
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MUb WMb) in FRH; [| cbn; clear - SPAH; lia].
  apply (fun H => bytes_at_transport _ _ _ _ _ _ H MUb) in SRC; [| rewrite SLEN, Z2Nat.id by lia; cbn; clear - DBC DH CEIL LO SPAL; lia].
  (* [comment removed for export] *)
  zstep. sfalse. zstep. sfalse. zstep. zstep. zstep.
  apply evt_done. eapply cps_step_same.
  { eapply (@asan_memcpy_cpsA (push AR f 1)) with (d := C) (s := D) (bs := src) (bd := bC) (bsrc := bD) (lo := lo) (OW := OW) (LB := LB);
      rewrite ?SLEN, ?Z2Nat.id by lia; rewrite ?ESPA; try reflexivity.
    - exact HEAPb.
    - exact STb.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
    - unfold RT_STACK. clear - LO SPAL. lia.
    - unfold USTACK_TOP. clear - TOP SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MIb.
    - exact CIN.
    - exact CL.
    - exact CH.
    - exact DIN.
    - exact DL.
    - exact DH.
    - exact SRC.
    - thaw SEP. clear - SEP. lia.
    - clear - LEN. lia. }
  intros msM PO. unfold icall_post in PO. rewrite ?ESPA in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & FM & fcM & mM & -> & MIM & STM & HEAPM & WMM & AGM & BZ & WRM).
  rewrite (ret_pc_even 0x248df4) by (clear; lia). unfold MallocRep.wz.
  rewrite !SLEN, !Z2Nat.id in AGM by (clear - LEN; lia). rewrite !SLEN, !Z2Nat.id in WRM by (clear - LEN; lia).
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGM) in FRLb; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia| clear - Hxa CBC CH CEIL LO SPAL; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in FRH; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia| clear - Hxa CBC CH CEIL LO SPAL SPAH; lia]].
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep.
  apply evt_done. change (Z_to_bv 64 2395680) with (wz AEI_EXIT).
  eapply (aei_epi_cps Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAPM| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STM| exact CEIL| clear - LO SPAL; lia
    | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIM
    | exact FRLb| exact FRH| reflexivity|].
  intros Σ' m' x11' HEAP' CR' LIVE' ST' MI' AG'. rewrite (v_addiw0_small len) by (clear - LEN; lia).
  eapply K; [exact HEAP'| rewrite CR'; exact CR1| rewrite LIVE'; exact EL1| exact ST'| exact MI'| |].
  - (* [comment removed for export] *)
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF| intros a [Ha _]; exact Ha]|].
    eapply agree_on_trans.
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUb)|]. intros a [Ha _]. cbn [outside fst snd]. split; [| exact I].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL CE1 LO SPAL; plia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEIL LO SPAL. plia. }
    eapply agree_on_trans.
    { eapply agree_on_mono; [exact AGM|]. intros a [Ha Hn]. split; [| exact Hn].
      destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha]. }
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _].
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
  - (* [comment removed for export] *)
    assert (DST : rw_cells ctasegs mM C [CB (Z.to_nat len) src]).
    { split; [split; [cbn; split; [exact SLEN| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BZ]|].
      cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WRM. }
    eapply rw_cells_agree; [exact AG'| exact DST|]. intros xa Hxa. cbn [cells_size csize] in Hxa. rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia.
    right; right. exists bC. split; [exact CIN| clear - Hxa CL CH; lia].
Qed.

End WithRT.
