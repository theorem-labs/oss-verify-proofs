(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import GDesc RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct RtCallA ImplA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApFrame W_strdup.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeKit TimeKit2 TimeFmtPure TimeToTmDefs TimeToTmFeb W_time_to_tm_it.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_time_leavesA W_posix_to_tmA Fr_ossl_asn1_time_to_tm W_time_to_tm_frontA TimeToTmDefsA W_time_to_tm_itA W_time_to_tm_BA W_time_to_tm_CA W_time_to_tm_DA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Section WithRT.
Context {AR : ARun}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.

Lemma t2t_acceptA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (bd bs btm : block) (DA GS tm ms : Z) (t : tm6) (tjunk : list byte),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + T2T_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FRM < FRAMES_MAX)%nat -> 1 <= rt_credit RTS Σ ->
  In bd (OW ++ LB) -> blk_addr bd <= DA -> DA + 16 <= blk_addr bd + blk_size bd -> DA mod 8 = 0 ->
  rw_cells ctasegs m DA [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] ->
  In bs (OW ++ LB) -> blk_addr bs <= GS -> GS + 19 <= blk_addr bs + blk_size bs -> GS mod 8 = 0 ->
  rw_cells ctasegs m GS (gcells t ms) -> tm_valid t -> 0 <= ms < 1000 ->
  0 <= tm < 2^64 ->
  (tm <> 0 -> In btm (OW ++ LB) /\ blk_addr btm <= tm /\ tm + 56 <= blk_addr btm + blk_size btm /\ rw_cells ctasegs m tm [CB 56%nat tjunk]) ->
  a0 = Z_to_bv 64 tm -> a1 = Z_to_bv 64 DA ->
  (forall (Σ' : rts RTS) (m' : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RTS Σ' = rt_credit RTS Σ - 1 -> rt_live RTS Σ' = rt_live RTS Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ (tm = 0 \/ ~ (tm <= a < tm + 56))) m m' ->
     (tm <> 0 -> exists wd yd, rw_cells ctasegs m' tm (TM_CELLS_A (t_sec t) (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd)) ->
     cps ctasegs (ASTA RTS Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_ASN1_TIME_TO_TM_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until tjunk. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED HIND D1 D2 ALD HD HINS S1 S2 ALS HS TV MSR Htm HTM -> -> K.
  assert (Hl : 15 <= 19 < 2^31) by (clear; lia).
  unfold T2T_STACK_A, RT_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in TOP.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIND) as (A0 & _ & _ & AC & AI).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  change (Z_to_bv 64 OSSL_ASN1_TIME_TO_TM_A) with (wz T2T_ENTRY).
  eapply (t2t_pro_cps Q) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP| exact ST| exact CEIL| unfold T2T_FRAME, RT_STACK; clear - LO; lia| unfold USTACK_TOP; exact TOP| exact AL16
    | rewrite unsigned_lit by (clear - A0 AC D1 D2 C3; unfold BnHeapA.ACEIL in *; lia); clear - A0 D1; lia              (* [comment removed for export] *)
    | rewrite unsigned_lit by (clear - A0 AC D1 D2 C3; unfold BnHeapA.ACEIL in *; lia); exact ALD                            (* [comment removed for export] *)
    | exact MI| reflexivity| exact FLEN| exact CRED|].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j192 j200 j208 jf24 jf32 jf88
         HEAP3 FRESH GEO CR1 LIVE1 ST3 MI3 AGF LOW HIGH FRC SHC SPA32 SPAL SPAH GSZ SAVJ.
  unfold T2T_BODY, MallocRep.wz.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3. unfold SEGTOP_A in G4.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO CEIL C1; alia).
  pose proof (FRESH _ HIND) as OFA. unfold off_fr in OFA. change (fs_size 1) with 128 in OFA.
  (* [comment removed for export] *)
  pose proof HD as HD0.
  apply (rw_cells_agree _ _ _ _ _ AGF) in HD; [| intros xa Hxa; right; right; exists bd; split; [exact HIND| cbn in Hxa; lia]].
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [q Hq].
  pose proof (t2t_open_tmp Σ1 OW LB m3 f q HEAP3 FRESH GEO SHC Hq) as HEAPo.
  assert (HIND' : In bd (OW ++ (q, f + 32, 56) :: LB)) by (apply in_app_or in HIND as [?|?]; apply in_or_app; [left; assumption| right; right; assumption]).
  assert (HINT : In (q, f + 32, 56) (OW ++ (q, f + 32, 56) :: LB)) by (apply in_or_app; right; left; reflexivity).
  ablock HEAPo HIND' ACCD OFFD. ablock HEAPo HINT ACCT OFFT.
  destruct (@AH_shb (push AR f 1) _ _ _ _ HEAPo) as [SHB1 SHB2].
  pose proof (munch_refl [(spa, spa + 232); (f + 32, f + 32 + 56)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  assert (OFF3 : offshW [(spa, spa + 232); (f + 32, f + 32 + 56)]%Z) by (cbn [offshW]; clear - SPAL SPAH CEILu LO C1 C2 C3 G1 G3 G4 G5; plia).
  assert (EDA : bv_unsigned (Z_to_bv 64 DA) = DA) by (apply unsigned_lit; clear - A0 AC D1 D2 CEILu C3; lia).
  rewrite EDA in LOW |- *. clear SHC FRC.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  ab_shload 4. step. rstep. rewrite ?zxb_z8, ?sxb_z8. if_false. step. rewrite (sx32_small 24) by (clear; lia). step. step. brc. step. step. brc.
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  step. rewrite (zx32_small 19) by (clear - Hl; lia).
  step.
  (* [comment removed for export] *)
  step. step. step. try (rewrite (addiw_small 19 0), Z.add_0_r by (clear - Hl; lia)). step. step. step.
  name_mem m1.
  match goal with H : munch _ m3 m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m3 m1 |- _ => rename H into WM1 end.
  assert (AWO : Forall (@aclient_write_ok (push AR f 1) (OW ++ (q, f + 32, 56) :: LB)) [(spa, spa + 232); (f + 32, f + 32 + 56)]%Z).
  { constructor; [left; cbn [fst snd]; clear - CEILu LO SPAL SPAH TOP GSZ; plia|].
    constructor; [right; right; exists (q, f + 32, 56); split; [exact HINT| cbn; clear; lia]| constructor]. }
  assert (HEAP1 : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 32, 56) :: LB) m1) by (eapply (@AH_frame (push AR f 1)); [exact HEAPo| exact MU1| exact WM1| exact AWO]).
  apply evt_done. eapply cps_step_same.
  { eapply (@asan_memset_cpsA (push AR f 1) _ (Z_to_bv 64 spa)) with (d := f + 32) (n := 56) (c := Z_to_bv 8 0) (bd := (q, f + 32, 56)) (lo := lo) (OW := OW) (LB := (q, f + 32, 56) :: LB);
      rewrite ?ESPA; try reflexivity.
    - exact HEAP1.
    - match goal with H : stk ctasegs m1 _ _ |- _ => exact H end.
    - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
    - unfold RT_STACK. clear - LO SPAL. lia.
    - unfold USTACK_TOP. clear - TOP SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - match goal with H : mem_inv ctasegs m1 |- _ => exact H end.
    - exact HINT.
    - cbn [blk_addr blk_size fst snd]. clear; lia. }
  intros msM PO. unfold icall_post in PO. rewrite ?ESPA in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & BZ & WRM).
  rewrite (ret_pc_even 0x26edf4) by (clear; lia). unfold MallocRep.wz. cbn [ar_PMc push amb].
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGM) in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia| clear - Hxa G3 CEILu LO SPAL SPAH GSZ; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia| clear - Hxa G3 CEILu LO SPAL SPAH; lia]].
  clear ACCD ACCT OFFD OFFT SHB1 SHB2 HEAP1. try clear OFF3. try clear WM3.
  pose proof (munch_refl [(spa, spa + 232)]%Z mM) as MUM. pose proof (wmono_refl ctasegs mM) as WMM'.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  pose proof (zero56_of_memset mM (f + 32) BZ WRM) as TMP. cbn [app] in TMP. clear BZ WRM.
  step. brc.
  assert (SEPT : f + 32 + 56 <= spa - 16 \/ spa + 304 <= f + 32) by (clear - G3 CEILu LO SPAL; lia).
  do 46 zstep.
  pose proof (AH_range_gen _ _ _ _ bs HEAP HINS) as (B0 & _ & _ & BC & BI).
  (* [comment removed for export] *)
  rewrite ?(sx32_small 0) in LOW by (clear; lia).
  name_mem mH.
  match goal with H : munch _ mM mH |- _ => rename H into MUH end. match goal with H : wmono ctasegs mM mH |- _ => rename H into WMH end.
  match goal with H : stk ctasegs mH _ _ |- _ => rename H into STH end. match goal with H : mem_inv ctasegs mH |- _ => rename H into MIH end.
  (* [comment removed for export] *)
  assert (OFFH : offshW [(spa, spa + 232)]%Z) by (cbn [offshW]; clear - SPAL SPAH CEILu LO C1 C2 C3; alia).
  assert (HINS' : In bs (OW ++ (q, f + 32, 56) :: LB)) by (apply in_app_or in HINS as [?|?]; apply in_or_app; [left; assumption| right; right; assumption]).
  pose proof (FRESH _ HINS) as OFS. unfold off_fr in OFS. change (fs_size 1) with 128 in OFS.
  ablock HEAPM HIND' ACCD0 OFFD0. ablock HEAPM HINS' ACCS0 OFFS0.
  assert (ACCD : acc ctasegs mH DA 16).
  { eapply (acc_munch ctasegs _ mM mH); [eapply acc_sub; [exact ACCD0| exact D1| exact D2]| exact MUH| exact OFFH| clear - A0 D1; lia| clear - AC D2 C3; alia]. }
  assert (ACCS : acc ctasegs mH GS 19).
  { eapply (acc_munch ctasegs _ mM mH); [eapply acc_sub; [exact ACCS0| exact S1| exact S2]| exact MUH| exact OFFH| clear - B0 S1; lia| clear - BC S2 C3; alia]. }
  pose proof (@AH_art (push AR f 1) _ _ _ _ HEAPM) as ARTM. cbn [ar_RT push amb] in ARTM.
  assert (ACCMIN : acc ctasegs mH A_MINTAB_A 36).
  { eapply (acc_munch ctasegs _ mM mH); [eapply (af_lib_acc_lit RTS (@ar_AF AR) Σ1 mM (0x76b40, 36, 96)); [exact ARTM| vm_compute; reflexivity| unfold A_MINTAB_A; cbn; clear; lia| unfold A_MINTAB_A; cbn; clear; lia]
      | exact MUH| exact OFFH| unfold A_MINTAB_A; clear; lia| unfold A_MINTAB_A; clear; lia]. }
  assert (ACCMAX : acc ctasegs mH A_MAXTAB_A 36).
  { eapply (acc_munch ctasegs _ mM mH); [eapply (af_lib_acc_lit RTS (@ar_AF AR) Σ1 mM (0x76ba0, 36, 96)); [exact ARTM| vm_compute; reflexivity| unfold A_MAXTAB_A; cbn; clear; lia| unfold A_MAXTAB_A; cbn; clear; lia]
      | exact MUH| exact OFFH| unfold A_MAXTAB_A; clear; lia| unfold A_MAXTAB_A; clear; lia]. }
  assert (ACCMD : acc ctasegs mH A_MDAYS_A 48).
  { eapply (acc_munch ctasegs _ mM mH); [eapply (af_lib_acc_lit RTS (@ar_AF AR) Σ1 mM (0x76c00, 48, 96)); [exact ARTM| vm_compute; reflexivity| unfold A_MDAYS_A; cbn; clear; lia| unfold A_MDAYS_A; cbn; clear; lia]
      | exact MUH| exact OFFH| unfold A_MDAYS_A; clear; lia| unfold A_MDAYS_A; clear; lia]. }
  assert (ACCYD : acc ctasegs mH A_YDAYS_A 48).
  { eapply (acc_munch ctasegs _ mM mH); [eapply (af_lib_acc_lit RTS (@ar_AF AR) Σ1 mM (0x76ea0, 48, 96)); [exact ARTM| vm_compute; reflexivity| unfold A_YDAYS_A; cbn; clear; lia| unfold A_YDAYS_A; cbn; clear; lia]
      | exact MUH| exact OFFH| unfold A_YDAYS_A; clear; lia| unfold A_YDAYS_A; clear; lia]. }
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGF) in HS; [| intros xa Hxa; right; right; exists bs; split; [exact HINS| unfold gcells, zb8 in Hxa; cbn in Hxa; clear - Hxa S1 S2; lia]].
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU1)) in HS; [| intros xa Hxa; unfold gcells, zb8 in Hxa; cbn in Hxa; cbn [outside]; clear - Hxa S1 S2 OFS BC CEILu LO SPAL; alia].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HS; [| intros xa Hxa; unfold gcells, zb8 in Hxa; cbn in Hxa; split; [right; right; exists bs; split; [exact HINS'| clear - Hxa S1 S2; lia]| clear - Hxa S1 S2 OFS; lia]].
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUH)) in HS; [| intros xa Hxa; unfold gcells, zb8 in Hxa; cbn in Hxa; cbn [outside]; clear - Hxa S1 S2 BC CEILu LO SPAL; alia].
  (* [comment removed for export] *)
  clear HD. rename HD0 into HD.
  apply (rw_cells_agree _ _ _ _ _ AGF) in HD; [| intros xa Hxa; right; right; exists bd; split; [exact HIND| cbn in Hxa; clear - Hxa D1 D2; lia]].
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU1)) in HD; [| intros xa Hxa; cbn in Hxa; cbn [outside]; clear - Hxa D1 D2 OFA AC CEILu LO SPAL; alia].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HD; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists bd; split; [exact HIND'| clear - Hxa D1 D2; lia]| clear - Hxa D1 D2 OFA; lia]].
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUH)) in HD; [| intros xa Hxa; cbn in Hxa; cbn [outside]; clear - Hxa D1 D2 AC CEILu LO SPAL; alia].
  (* [comment removed for export] *)
  assert (TMPc : rw_cells ctasegs mH (f + 32) (TM_CELLS_A 0 0 0 0 0 0 0 0)).
  { unfold TM_CELLS_A. eapply rw_cells_recast; [exact TMP| cbn; repeat split; reflexivity| reflexivity| reflexivity]. }
  clear TMP ACCD0 ACCS0 OFFD0 OFFS0 ARTM.
  assert (FOLDLOW : rw_cells ctasegs mH spa (t2t_lowA j0 j192 j200 19 tm f DA GS 0 0 g junk)) by (unfold t2t_lowA, MASK47; exact LOW). clear LOW.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (t2t_segBA _ sp gp) with (lo := lo) (ms := ms) (t := t); try eassumption;
      first [ exact CEIL | clear - LO SPAL; lia | unfold USTACK_TOP; clear - TOP SPAH; lia | clear - SPA32; uchk_open; Z.div_mod_to_equations; lia
            | clear - C1; alia | clear - C2; alia | clear - C3; alia | uchk_open; assumption
            | clear - A0 D1; lia | clear - AC D2; alia | clear - B0 S1; lia | clear - BC S2; alia
            | clear - G1; lia | clear - G3; alia | clear - G2; uchk_open; Z.div_mod_to_equations; lia | clear - G5; lia
            | clear - OFA D1 D2; lia | clear - OFS S1 S2; lia ]. }
  intros msB PO. unfold t2t_headA_post in PO.
  destruct PO as (y1 & y5 & y6 & y7 & y10 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y22 & y23 & y27 & y28 & y29 & y30 & y31 & mB & -> & MUB & WMB & MIB & STB & LOWB & TMPB).
  assert (OFFW : offshW [(lo, spa + 232); (f + 32, f + 32 + 56)]%Z) by (cbn [offshW]; assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption); clear - SPAL SPAH CEILu LO LO0 C1 C2 C3 G1 G3 G4 G5; alia).
  Local Ltac reseg mX mY MUXY OFFW HD HS ACCD ACCS ACCMIN ACCMAX ACCMD ACCYD D1 D2 S1 S2 A0 B0 AC BC OFA OFS CEILu LO SPAL TOP :=
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUXY)) in HD; [| intros xa Hxa; cbn in Hxa; cbn [outside]; split; [| split; [| exact I]]; clear - Hxa D1 D2 OFA AC CEILu LO SPAL; unfold BnHeapA.ACEIL in *; lia];
    apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUXY)) in HS; [| intros xa Hxa; unfold gcells, zb8 in Hxa; cbn in Hxa; cbn [outside]; split; [| split; [| exact I]]; clear - Hxa S1 S2 OFS BC CEILu LO SPAL; unfold BnHeapA.ACEIL in *; lia];
    eapply (acc_munch ctasegs _ mX mY) in ACCD; [| exact MUXY| exact OFFW| clear - D1 A0; lia| clear - D2 AC CEILu LO TOP; unfold BnHeapA.ACEIL in *; lia];
    eapply (acc_munch ctasegs _ mX mY) in ACCS; [| exact MUXY| exact OFFW| clear - S1 B0; lia| clear - S2 BC CEILu LO TOP; unfold BnHeapA.ACEIL in *; lia];
    eapply (acc_munch ctasegs _ mX mY) in ACCMIN; [| exact MUXY| exact OFFW| unfold A_MINTAB_A; clear; lia| unfold A_MINTAB_A; clear; lia];
    eapply (acc_munch ctasegs _ mX mY) in ACCMAX; [| exact MUXY| exact OFFW| unfold A_MAXTAB_A; clear; lia| unfold A_MAXTAB_A; clear; lia];
    eapply (acc_munch ctasegs _ mX mY) in ACCMD; [| exact MUXY| exact OFFW| unfold A_MDAYS_A; clear; lia| unfold A_MDAYS_A; clear; lia];
    eapply (acc_munch ctasegs _ mX mY) in ACCYD; [| exact MUXY| exact OFFW| unfold A_YDAYS_A; clear; lia| unfold A_YDAYS_A; clear; lia].
  reseg mH mB MUB OFFW HD HS ACCD ACCS ACCMIN ACCMAX ACCMD ACCYD D1 D2 S1 S2 A0 B0 AC BC OFA OFS CEILu LO SPAL TOP.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (t2t_segCA _ sp gp) with (lo := lo) (ms := ms) (t := t); try eassumption;
      first [ exact CEIL | clear - LO SPAL; lia | unfold USTACK_TOP; clear - TOP SPAH; lia | clear - SPA32; uchk_open; Z.div_mod_to_equations; lia
            | clear - C1; alia | clear - C2; alia | clear - C3; alia | uchk_open; assumption
            | clear - A0 D1; lia | clear - AC D2; alia | clear - B0 S1; lia | clear - BC S2; alia
            | clear - G1; lia | clear - G3; alia | clear - G2; uchk_open; Z.div_mod_to_equations; lia | clear - G5; lia
            | clear - OFA D1 D2; lia | clear - OFS S1 S2; lia ]. }
  intros msC (wd & yd & PO). unfold t2t_headA_post in PO.
  destruct PO as (z1 & z5 & z6 & z7 & z10 & z12 & z13 & z14 & z15 & z16 & z17 & z18 & z19 & z22 & z23 & z27 & z28 & z29 & z30 & z31 & mC & -> & MUC & WMC & MIC & STC & LOWC & TMPC).
  reseg mB mC MUC OFFW HD HS ACCD ACCS ACCMIN ACCMAX ACCMD ACCYD D1 D2 S1 S2 A0 B0 AC BC OFA OFS CEILu LO SPAL TOP.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (t2t_segDA _ sp gp) with (lo := lo) (ms := ms) (t := t) (tm := tm); try eassumption;
      first [ exact CEIL | clear - LO SPAL; lia | unfold USTACK_TOP; clear - TOP SPAH; lia | clear - SPA32; uchk_open; Z.div_mod_to_equations; lia
            | clear - C1; alia | clear - C2; alia | clear - C3; alia | uchk_open; assumption
            | clear - A0 D1; lia | clear - AC D2; alia | clear - B0 S1; lia | clear - BC S2; alia
            | clear - G1; lia | clear - G3; alia | clear - G2; uchk_open; Z.div_mod_to_equations; lia | clear - G5; lia
            | clear - OFA D1 D2; lia | clear - OFS S1 S2; lia | clear - Htm; lia ]. }
  intros msD PO. unfold t2t_finA_post in PO.
  destruct PO as (w1 & w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w20 & w21 & w23 & w27 & w28 & w29 & w30 & w31 & mD & -> & MUD & WMD & MID & STD & LOWD & TMPD).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (STKW : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a ->
            outside [(spa, spa + 232); (f + 32, f + 32 + 56)]%Z a /\ outside [(lo, spa + 232); (f + 32, f + 32 + 56)]%Z a).
  { intros a Ha. cbn [outside fst snd].
    assert (X1 : ~ lo <= a < spa + 232).
    { destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH GSZ; lia| |].
      + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL LO SPAL C1; alia.
      + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEIL LO SPAL. alia. }
    assert (X2 : ~ f + 32 <= a < f + 32 + 56).
    { destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO; lia| |].
      + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
      + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
    clear - X1 X2 LO SPAL. repeat split; try exact I; lia. }
  assert (LIFT : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ (q, f + 32, 56) :: LB) spa a).
  { intros a Ha. destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
    destruct Ha as (b & Hb & Hr). exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
  assert (AGD : agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a) m mD).
  { eapply agree_on_trans; [eapply agree_on_mono; [exact AGF| intros a Ha; exact Ha]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| intros a Ha; exact (proj1 (STKW a Ha))]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGM| intros a Ha; pose proof (STKW a Ha) as [O _]; cbn [outside fst snd] in O; split; [exact (LIFT a Ha)| clear - O; lia]]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUH)| intros a Ha; pose proof (STKW a Ha) as [O _]; cbn [outside fst snd] in O |- *; clear - O; tauto]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUB)| intros a Ha; exact (proj2 (STKW a Ha))]|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUC)| intros a Ha; exact (proj2 (STKW a Ha))]|].
    eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUD)| intros a Ha; exact (proj2 (STKW a Ha))]. }
  (* [comment removed for export] *)
  assert (MUHD : munch [(lo, spa + 232); (f + 32, f + 32 + 56)]%Z mH mD) by (eapply munch_trans; [exact MUB|]; eapply munch_trans; [exact MUC| exact MUD]).
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MUHD)) in HIGH; [| intros xa Hxa; cbn in Hxa; cbn [outside]; split; [| split; [| exact I]]; clear - Hxa SPAH SPAL G3 CEILu LO; lia].
  assert (MUMD : munch [(lo, spa + 232); (f + 32, f + 32 + 56)]%Z mM mD).
  { eapply munch_trans; [eapply munch_weaken; [| exact MUH]; unfold sub_fp; intros y Hy; clear - Hy LO SPAL; cbn [outside fst snd] in *; repeat split; try exact I; lia|].
    eapply munch_trans; [exact MUB|]. eapply munch_trans; [exact MUC| exact MUD]. }
  assert (WMMD : wmono ctasegs mM mD).
  { eapply wmono_trans; [exact WMH|]. eapply wmono_trans; [exact WMB|]. eapply wmono_trans; [exact WMC| exact WMD]. }
  assert (AWO' : Forall (@aclient_write_ok (push AR f 1) (OW ++ (q, f + 32, 56) :: LB)) [(lo, spa + 232); (f + 32, f + 32 + 56)]%Z).
  { constructor; [left; cbn [fst snd]; clear - CEILu LO SPAL SPAH TOP GSZ; plia|].
    constructor; [right; right; exists (q, f + 32, 56); split; [exact HINT| cbn; clear; lia]| constructor]. }
  assert (HEAPD : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 32, 56) :: LB) mD) by (eapply (@AH_frame (push AR f 1)); [exact HEAPM| exact MUMD| exact WMMD| exact AWO']).
  clear ACCD ACCS ACCMIN ACCMAX ACCMD ACCYD HD HS LOWB LOWC TMPB TMPC.
  unfold t2t_lowA in LOWD.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evt_done.
  eapply (cps_step_same Σ1 _ (fun msE => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x27 x28 x29 x30 x31 : word) (FE : bvmap 5 word) (fcE : bv 32) (mE : mem),
       msE = MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp (Z_to_bv 64 spa) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 1) x23
                    (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x27 x28 x29 x30 x31) FE (wz T2T_EXIT) fcE None mE (seg_rom ctasegs)
       /\ @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 32, 56) :: LB) mE /\ stk ctasegs mE lo spa /\ mem_inv ctasegs mE
       /\ rw_cells ctasegs mE spa (t2t_lowA j0 j192 j200 19 tm f DA GS (t_mon t - 1) (t_year t - 1900) g junk)
       /\ rw_cells ctasegs mE (bv_unsigned sp + -16) [C8 s0; C8 ra]
       /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ (tm = 0 \/ ~ (tm <= a < tm + 56))) m mE
       /\ (tm <> 0 -> exists wd' yd', rw_cells ctasegs mE tm (TM_CELLS_A (t_sec t) (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd' yd')))).
  { destruct (Z.eq_dec tm 0) as [TM0|TMNZ].
    - (* [comment removed for export] *)
      subst tm. apply cps_from_evt'. step. brc.
      apply evt_done. apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
      do 24 eexists. exists mD. split; [reflexivity|].
      split; [exact HEAPD|]. split; [exact STD|]. split; [exact MID|]. split; [unfold t2t_lowA, MASK47; exact LOWD|]. split; [exact HIGH|].
      split; [eapply agree_on_mono; [exact AGD| intros a [Ha _]; exact Ha]|]. intros NZ. exfalso. apply NZ. reflexivity.
    - (* [comment removed for export] *)
      destruct (HTM TMNZ) as (HINTM & TM1 & TM2 & HT).
      pose proof (AH_range_gen _ _ _ _ btm HEAP HINTM) as (T0 & _ & _ & TC & _).
      pose proof (FRESH _ HINTM) as OFT. unfold off_fr in OFT. change (fs_size 1) with 128 in OFT.
      assert (HINTM' : In btm (OW ++ (q, f + 32, 56) :: LB)) by (apply in_app_or in HINTM as [?|?]; apply in_or_app; [left; assumption| right; right; assumption]).
      apply (rw_cells_agree _ _ _ _ _ AGD) in HT; [| intros xa Hxa; right; right; exists btm; split; [exact HINTM| cbn in Hxa; clear - Hxa TM1 TM2; lia]].
      assert (ETM : bv_unsigned (Z_to_bv 64 tm) = tm) by (apply unsigned_lit; clear - Htm; lia).
      assert (LTM : Z.of_nat (length (cells_bytes (TM_CELLS_A (t_sec t) (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd))) = 56)
        by (rewrite cells_bytes_length; [reflexivity| cbn; repeat split; reflexivity]).
      apply cps_from_evt'.
      step. if_cases KT; zify_cond KT; [exfalso; rewrite ?ETM, ?unsigned_lit in KT by (clear - Htm; lia); clear - KT TMNZ; lia|]. clear KT.
      step. step. step. step.
      apply evt_done. eapply cps_step_same.
      { eapply (@asan_memcpy_cpsA (push AR f 1) _ (Z_to_bv 64 spa)) with (d := tm) (s := f + 32) (bd := btm) (bsrc := (q, f + 32, 56)) (lo := lo) (OW := OW) (LB := (q, f + 32, 56) :: LB)
            (bs := cells_bytes (TM_CELLS_A (t_sec t) (t_min t) (t_hour t) (t_mday t) (t_mon t - 1) (t_year t - 1900) wd yd)); rewrite ?ESPA; try reflexivity.
        - exact HEAPD.
        - exact STD.
        - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
        - unfold RT_STACK. clear - LO SPAL. lia.
        - unfold USTACK_TOP. clear - TOP SPAH. lia.
        - clear - SPA32. Z.div_mod_to_equations. lia.
        - exact MID.
        - exact HINTM'.
        - exact TM1.
        - rewrite LTM. clear - TM2. lia.
        - exact HINT.
        - destruct TMPD as [[_ BY] _]. exact BY.
        - rewrite LTM. clear - OFT TM1 TM2. lia. }
      intros msM2 PO. unfold icall_post in PO. rewrite ?ESPA in PO.
      destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & FE & fcE & mE & -> & MIE & STE & HEAPE & WME & AGE & BYE & WRE).
      rewrite (ret_pc_even 0x26f440) by (clear; lia). unfold MallocRep.wz. cbn [ar_PMc push amb]. rewrite ?LTM in AGE, WRE.
      apply (rw_cells_agree _ _ _ _ _ AGE) in LOWD; [| intros xa Hxa; cbn [cells_size csize length Nat.add] in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia| clear - Hxa TM2 TC CEILu LO SPAL; unfold BnHeapA.ACEIL in *; lia]].
      apply (rw_cells_agree _ _ _ _ _ AGE) in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia| clear - Hxa TM2 TC CEILu LO SPAL SPAH; unfold BnHeapA.ACEIL in *; lia]].
      apply cps_from_evt'. step.
      apply evt_done. apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
      do 24 eexists. exists mE. split; [reflexivity|].
      split; [exact HEAPE|]. split; [exact STE|]. split; [exact MIE|]. split; [unfold t2t_lowA, MASK47; exact LOWD|]. split; [exact HIGH|].
      split.
      + eapply agree_on_trans; [eapply agree_on_mono; [exact AGD| intros a [Ha _]; exact Ha]|].
        eapply agree_on_mono; [exact AGE|]. intros a [Ha Hn]. split; [exact (LIFT a Ha)|]. destruct Hn as [Hn|Hn]; [exfalso; exact (TMNZ Hn)| exact Hn].
      + intros _. exists wd, yd. unfold TM_CELLS_A.
        eapply rw_cells_recast; [exact (rw_cells_of_bytes _ _ _ BYE WRE)| cbn; repeat split; reflexivity| reflexivity| reflexivity]. }
  intros msE PO.
  destruct PO as (ee1 & ee5 & ee6 & ee7 & ee10 & ee11 & ee12 & ee13 & ee14 & ee15 & ee16 & ee17 & ee18 & ee19 & ee20 & ee21 & ee23 & ee27 & ee28 & ee29 & ee30 & ee31 & FE & fcE & mE & -> & HEAPE & STE & MIE & LOWE & HIGHE & AGE & HTE).
  (* [comment removed for export] *)
  pose proof HEAPE as HEAP5.
  eapply (@frame_obj_close (push AR f 1)) in HEAP5; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
  unfold t2t_lowA in LOWE.
  eapply (t2t_epi_cps Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAP5| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| first [exact STE| rewrite <- ?ESPA; exact STE]| exact CEIL| clear - LO SPAL; lia
    | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIE
    | eapply (rw_cells_recast mE spa _ _ LOWE); [| reflexivity| reflexivity]; pose proof (proj1 (proj1 LOWE)) as WF; cbn in WF; cbn; repeat split; try reflexivity; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption
    | exact HIGHE| reflexivity|].
  intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
  eapply K; [exact HEAP'| rewrite CR'; exact CR1| rewrite LIVE'; exact LIVE1| exact ST'| exact MI'| |].
  - eapply agree_on_trans; [exact AGE|]. eapply agree_on_mono; [exact AG'|]. intros a [Ha _].
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
  - intros NZ. destruct (HTE NZ) as (wd' & yd' & HT'). exists wd', yd'.
    destruct (HTM NZ) as (HINTM & TM1 & TM2 & _).
    eapply (rw_cells_agree _ _ _ _ _ AG'); [exact HT'|]. intros xa Hxa. right; right. exists btm. split; [exact HINTM|]. unfold TM_CELLS_A in Hxa. cbn in Hxa. clear - Hxa TM1 TM2. lia.
Qed.

End WithRT.
