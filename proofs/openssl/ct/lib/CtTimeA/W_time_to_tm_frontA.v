(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct RtCallA ImplA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_posix_to_tmA Fr_ossl_asn1_time_to_tm.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
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
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.

(* [comment removed for export] *)
Definition T2T_STACK_A : Z := 336 + RT_STACK.        (* [comment removed for export] *)
Definition T2T_BGE : Z := 0x26edf4.          (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma t2t_open_tmp : forall Σ1 OW LB m3 f q,
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 1 b) -> @fr_geo (push AR f 1) f 1 ->
  rw_cells ctasegs m3 (shad f) t2t_shadow_pro -> ~ In q (map blk_id (OW ++ LB)) ->
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 32, 56) :: LB) m3.
Proof.
  intros Σ1 OW LB m3 f q HEAP FRESH GEO FRS Hq.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 1) Σ1 OW LB m3 f 1%nat q (f + 32) 56 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 1) with 128; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m3 (shad f) t2t_shadow_pro 4%nat (f + 32) 56 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 1) with 128 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma t2t_rejectA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (bd : block) (DA l GS tm : Z),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + T2T_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FRM < FRAMES_MAX)%nat -> 1 <= rt_credit RTS Σ ->
  In bd (OW ++ LB) -> blk_addr bd <= DA -> DA + 16 <= blk_addr bd + blk_size bd -> DA mod 8 = 0 ->
  rw_cells ctasegs m DA [C4 (Z_to_bv 64 l); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)] ->
  0 <= l < 15 -> 0 <= tm < 2^64 ->
  a0 = Z_to_bv 64 tm -> a1 = Z_to_bv 64 DA ->
  (forall (Σ' : rts RTS) (m' : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RTS Σ' = rt_credit RTS Σ - 1 -> rt_live RTS Σ' = rt_live RTS Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m' ->
     cps ctasegs (ASTA RTS Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_ASN1_TIME_TO_TM_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until tm. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED HIND D1 D2 ALD HD Hl Htm -> -> K.
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
  step. rewrite (zx32_small l) by (clear - Hl; lia).
  step.
  (* [comment removed for export] *)
  step. step. step. rewrite (addiw_small l 0), Z.add_0_r by (clear - Hl; lia). step. step. step.
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
  step. if_cases KL; zify_cond KL; [exfalso; rewrite ?ab_signed_small, ?unsigned_lit in KL by (clear - Hl; lia); clear - KL Hl; lia|]. clear KL.
  step.
  step.
  assert (HEAPM' : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 32, 56) :: LB) mM) by exact HEAPM.
  assert (AGM' : agree_on (fun a => (aclient_addr (OW ++ (q, f + 32, 56) :: LB) spa a /\ ~ (f + 32 <= a < f + 32 + 56)) /\ ~ (spa <= a < spa + 232)) m1 mM)
    by (eapply agree_on_mono; [exact AGM| intros a [Ha _]; exact Ha]).
  clear AGM; rename AGM' into AGM; clear HEAPM.
  pose proof HEAPM' as HEAP5.
  eapply (@frame_obj_close (push AR f 1)) in HEAP5; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
  apply evt_done.
  change (Z_to_bv 64 0x26f648) with (wz T2T_EXIT).
  eapply (t2t_epi_cps Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAP5| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| first [exact STM| rewrite <- ?ESPA; exact STM]| exact CEIL| clear - LO SPAL; lia
    | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIM
    | eapply (rw_cells_recast mM spa _ _ LOW); [| reflexivity| reflexivity]; pose proof (proj1 (proj1 LOW)) as WF; cbn in WF; cbn; repeat split; try reflexivity; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption
    | exact HIGH| reflexivity|].
  intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
  eapply K; [exact HEAP'| rewrite CR'; exact CR1| rewrite LIVE'; exact LIVE1| exact ST'| exact MI'|].
  (* [comment removed for export] *)
  assert (STKW : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> outside [(spa, spa + 232); (f + 32, f + 32 + 56)]%Z a).
  { intros a Ha. cbn [outside fst snd]. split; [| split; [| exact I]].
    - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha SPAH GSZ; lia| |].
      + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEIL LO SPAL C1; alia.
      + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEIL LO SPAL. alia.
    - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEILu LO; lia| |].
      + destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
      + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
  eapply agree_on_trans; [eapply agree_on_mono; [exact AGF| intros a Ha; exact Ha]|].
  eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)| exact STKW]|].
  eapply agree_on_trans.
  { eapply agree_on_mono; [exact AGM|]. intros a Ha. pose proof (STKW a Ha) as O. cbn [outside fst snd] in O. split; [| clear - O; lia]. split; [| clear - O; lia].
    destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right].
    destruct Ha as (b & Hb & Hr). exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
  eapply agree_on_mono; [exact AG'|]. intros a Ha.
  destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
Qed.

End WithRT.
