(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog BnBase BnModel BnTree ApBase ApLogic ApPrim CtTime.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct RtCallA ImplA ImplAX BnIfaceA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import RtGenStmtA W_crypto_reallocA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_lkit R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApFrame W_akit W_prefix_create W_strdup W_bio_push Fr_bio_write_intern W_bio_write Fr_BIO_vprintf Fr_BIO_printf W_bio_printf W_bio_printf2 W_bio_vprintfxA W_bio_printfx8A.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import PrintfModel PrintfModelX ApFmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt Printf_lib Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import I_vsnstmt GDesc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs TimePrnFmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_time_leavesA Fr_ossl_asn1_time_to_tm W_time_to_tm_frontA TimeToTmDefsA W_time_to_tmA Fr_ossl_asn1_time_print_ex.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac rzstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.    (* [comment removed for export] *)
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
Ltac notake := let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; repeat (rewrite Z.shiftl_mul_pow2 in K by lia); rewrite ?land64 in K; rewrite ?unsigned_lit in K by lia; first [lia | apply K; reflexivity] |]; try clear K.

Definition A_C16_A : Z := 0x76d60.      (* [comment removed for export] *)
Definition A_MON_A : Z := 0x76dc0.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition GENTIME_PRINT_STACK_A : Z := 16 + 176 + 16 + BIO_PRINTF_NULL_STACK.

Lemma fmt_C16_roA : ro_bytes ctasegs A_C16_A (zb FMT_C16). Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma monA_ro : forall k, 0 <= k <= 11 -> ro_bytes ctasegs (4 * k + A_MON_A) (zb (mon_str k) ++ Z_to_bv 8 0 :: mon_slack k).
Proof.
  intros k Hk. assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; (apply ro_bytes_b_sound; vm_compute; reflexivity).
Qed.
Lemma monA_slack_ok : forall k, 0 <= k <= 11 -> (- (4 * k + A_MON_A + 3 + 1)) mod 8 <= zlength (mon_slack k) /\ zlength (mon_slack k) <= 4.
Proof.
  intros k Hk. assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; (cbv; split; discriminate).
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis PFC : printf_contracts RTS.

(* [comment removed for export] *)
Lemma vfmtA_C16 : forall (t : tm6) (ms : Z), tm_valid t -> 0 <= ms < 1000 ->
  exists o, zlength o = 24 + zdigits (t_year t) /\
  vfmtA_ok A_C16_A FMT_C16 [PA_s (mon_str (t_mon t - 1)); PA_i (t_mday t); PA_i (t_hour t); PA_i (t_min t); PA_i (t_sec t); PA_i 3; PA_s (dec3 ms); PA_i (t_year t)] o.
Proof.
  intros t ms TV MSR. pose proof TV as (Y & MO & MD & HH & MI' & SS).
  pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  destruct (mon_str_len (t_mon t - 1) ltac:(lia)) as [ML MR].
  assert (DL : zlength (dec3 ms) = 3) by reflexivity.
  destruct (printf_piecesx_C16 (mon_str (t_mon t - 1)) (t_mday t) (t_hour t) (t_min t) (t_sec t) (dec3 ms) (t_year t)
              ML ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite DL; lia) ltac:(lia)) as (ps & P).
  pose proof (printf_piecesx_count _ _ _ _ P) as L. pose proof (zdigits_le4 (t_year t) ltac:(lia)) as ZD. pose proof (zdigits_range (t_year t) ltac:(lia)) as ZR.
  exists (concat ps). split; [exact L|].
  split; [exact fmt_C16_roA|]. split; [exact fmt_bytes_C16|].
  split; [unfold A_C16_A; clear; lia|]. split; [unfold A_C16_A; change (zlength FMT_C16) with 34; cbv; discriminate|].
  split. { intros AR' Σ' OW' LB' m' H. change (zlength FMT_C16) with 34.
           eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' (0x76d60, 34, 96)); [exact (@AH_art AR' _ _ _ _ H)| vm_compute; reflexivity| unfold A_C16_A; cbn; clear; lia| unfold A_C16_A; cbn; clear; lia]. }
  split; [exact pass1x_ok_C16|].
  split. { rewrite L. apply (printf_modelx_sn _ _ _ _ P). rewrite L. unfold OssFuzzTheorems.Proofs.openssl.ct.lib.P.F_printf_iface.SN_CAP. clear - ZD ZR. lia. }
  split; [apply fp_callsx_nog; repeat constructor|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mon_vargA : forall OW LB m k, 0 <= k <= 11 -> vargA_ok OW LB m (Z_to_bv 64 (4 * k + A_MON_A)) (PA_s (mon_str k)).
Proof.
  intros OW LB m k Hk. destruct (mon_str_len k Hk) as [ML MR]. pose proof (monA_slack_ok k Hk) as [SK1 SK2].
  cbn [vargA_ok]. exists (mon_slack k). rewrite unsigned_lit by (unfold A_MON_A; lia). rewrite ML.
  split; [exact MR|]. split; [clear; lia|]. split; [exact SK1|].
  right. split; [unfold A_MON_A; lia|]. split; [rewrite (proj2 (monA_slack_ok k Hk)) || idtac; unfold A_MON_A; pose proof SK2; cbv [SEGTOP_A RT_iface.SEGTOP_A]; lia|]. split; [exact (monA_ro k Hk)|].
  intros AR' Σ' m' H. eapply (af_lib_acc_lit _ (@ar_AF AR') Σ' m' (0x76dc0, 48, 96)); [exact (@AH_art AR' _ _ _ _ H)| vm_compute; reflexivity| unfold A_MON_A; cbn; lia| unfold A_MON_A; cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma tpx_open_stm : forall Σ1 OW LB m3 f q,
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m3 -> (forall b, In b (OW ++ LB) -> off_fr f 1 b) -> @fr_geo (push AR f 1) f 1 ->
  rw_cells ctasegs m3 (shad f) tpx_shadow_pro -> ~ In q (map blk_id (OW ++ LB)) ->
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 32, 56) :: LB) m3.
Proof.
  intros Σ1 OW LB m3 f q HEAP FRESH GEO FRS Hq.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 1) Σ1 OW LB m3 f 1%nat q (f + 32) 56 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 1) with 128; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m3 (shad f) tpx_shadow_pro 4%nat (f + 32) 56 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 1) with 128 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gentime_printA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RTS) (OW LB : list block) (lo : Z)
    (gb pd pb : bptr) (G D out pv nw ts : Z) (t : tm6),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + GENTIME_PRINT_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (S (S (length FRM))) < FRAMES_MAX)%nat -> 5 <= rt_credit RTS Σ ->
  In (gb, G, ASN1_STRING_SIZE) OW -> rw_cells ctasegs m G (asn1_string_cells 19 V_ASN1_GENERALIZEDTIME D 0) ->
  In (pd, D, 19) OW -> rw_cells ctasegs m D [CB 19%nat (zb (genstr ts))] -> gentime_adj ts = Some t -> 0 <= ts < 2^64 ->
  In (pb, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 G ->
  (forall (Σ' : rts RTS) (m' : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (r : Z),
     0 <= r <= 28 ->
     AHEAP Σ' OW LB m' -> rt_credit RTS Σ - 5 <= rt_credit RTS Σ' -> rt_live RTS Σ' = rt_live RTS Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     apres_ex LB OW (bv_unsigned sp) [(out, out + BIO_SIZE)]%Z m m' ->
     rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv (nw + r)) ->
     cps ctasegs (ASTA RTS Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASN1_GENERALIZEDTIME_PRINT_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until t. intros HEAP ST CEIL LO TOP AL16 MI -> FLEN CRED HGIN HG HDIN HD GA TSR HBIN HB NW -> -> K.
  pose proof LO as LO'. unfold GENTIME_PRINT_STACK_A, BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK in LO'.
  unfold ASN1_STRING_SIZE, BIO_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (Cq1 & Cq2 & Cq3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (HGIN' : In (gb, G, 24) (OW ++ LB)) by (apply in_or_app; left; exact HGIN).
  assert (HDIN' : In (pd, D, 19) (OW ++ LB)) by (apply in_or_app; left; exact HDIN).
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HGIN') as (BG0 & _ & _ & BGC & BGI). cbn [blk_addr blk_size fst snd] in BG0, BGC, BGI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HDIN') as (BD0 & _ & _ & BDC & BDI). cbn [blk_addr blk_size fst snd] in BD0, BDC, BDI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BBC & BBI). cbn [blk_addr blk_size fst snd] in BB0, BBC, BBI.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HGIN)) as ALG. pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HDIN)) as ALD.
  assert (PR : printable ts = true) by (unfold printable; rewrite GA; reflexivity).
  pose proof (gentime_adj_valid ts t GA) as TV. pose proof (ts_ms_range ts) as MSR. pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS).
  assert (EG : bv_unsigned (Z_to_bv 64 G) = G) by (apply unsigned_lit; clear - BG0 BGC Cq3; alia).
  unfold asn1_string_cells, MallocRep.wz in HG. unfold bio_null_cells, bio_cells, MallocRep.wz in HB.
  pose proof HG as HG0. pose proof HD as HD0. pose proof HB as HB0.
  lazymatch type of HG0 with ?T => change (frozen T) in HG0 end. lazymatch type of HD0 with ?T => change (frozen T) in HD0 end. lazymatch type of HB0 with ?T => change (frozen T) in HB0 end.
  (* [comment removed for export] *)
  lazymatch type of BGI with ?T => change (frozen T) in BGI end. lazymatch type of BDI with ?T => change (frozen T) in BDI end. lazymatch type of BBI with ?T => change (frozen T) in BBI end.
  ablock HEAP HGIN' ACCG OFFG.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 32, bv_unsigned sp)]%Z) by (cbn [offshW]; clear - Cq1 Cq2 Cq3 CEILu LO' TOPu; alia).
  assert (SEPG : G + 24 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= G) by (clear - BGC CEILu LO'; alia).
  apply cps_from_evt'.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step.
  step. try rewrite (sx32_small 24) by (clear; lia). step. step. brc.
  do 2 step. step. release_frame FR ST (bv_unsigned sp). step.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 5 step. step.
  rename FR into FR0.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  match goal with H : stk ctasegs m1 _ _ |- _ => rename H into ST1 end. match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; clear - SPR LO' LO0; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a Ha. cbn [outside fst snd]. split; [| exact I].
    destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia| |].
    - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' Cq1; alia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). clear - Hr B3' CEILu LO'. alia. }
  clear ACCG OFFG SHB1 SHB2.
  (* [comment removed for export] *)
  apply evt_done. change (Z_to_bv 64 2554952) with (wz TPX_ENTRY).
  eapply (tpx_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP1| rewrite ESP; exact ST1| exact CEIL| rewrite ESP; unfold TPX_FRAME, RT_STACK; clear - LO'; lia| rewrite ESP; clear - TOPu; unfold USTACK_TOP; lia
    | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia| exact MI1| reflexivity| clear - FLEN; lia| clear - CRED; lia|].
  clear junk.
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 j16 j24 j32 j40 jf24 jf32 jf88
         HEAP3 FRESH GEO CR1 LIVE1 ST3 MI3 AGF LOW HIGH FRC SHC SPA32 SPAL SPAH GSZ SAVJ.
  rewrite ?ESP in AGF, HIGH, SPAL, SPAH, GSZ. unfold TPX_BODY, MallocRep.wz.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G5. unfold BnHeapA.ACEIL in G3. cbn [ar_SP0 push amb] in G3. unfold SEGTOP_A in G4.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO' CEIL Cq1; alia).
  pose proof (FRESH _ HGIN') as OFG. unfold off_fr in OFG. change (fs_size 1) with 128 in OFG. cbn [blk_addr blk_size fst snd] in OFG.
  pose proof (FRESH _ HDIN') as OFD. unfold off_fr in OFD. change (fs_size 1) with 128 in OFD. cbn [blk_addr blk_size fst snd] in OFD.
  pose proof (FRESH _ HBIN') as OFB. unfold off_fr in OFB. change (fs_size 1) with 128 in OFB. cbn [blk_addr blk_size fst snd] in OFB.
  lazymatch type of G5 with ?T => change (frozen T) in G5 end.
  (* [comment removed for export] *)
  assert (AG3 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3).
  { eapply agree_on_trans; [exact AG1|]. eapply agree_on_mono; [exact AGF|]. intros a Ha. destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha]. }
  try clear HG. try clear HD. try clear HB. unfold frozen in HG0, HD0, HB0. rename HG0 into HG. rename HD0 into HD. rename HB0 into HB.
  apply (rw_cells_agree _ _ _ _ _ AG3) in HG; [| intros xa Hxa; right; right; exists (gb, G, 24); split; [exact HGIN'| cbn; cbn in Hxa; clear - Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG3) in HD; [| intros xa Hxa; right; right; exists (pd, D, 19); split; [exact HDIN'| cbn; cbn in Hxa; clear - Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG3) in HB; [| intros xa Hxa; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; cbn in Hxa; clear - Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AGF) in FR0; [| intros xa Hxa; left; cbn in Hxa; clear - Hxa TOPu; unfold USTACK_TOP; lia].
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [q Hq].
  pose proof (tpx_open_stm Σ1 OW LB m3 f q HEAP3 FRESH GEO SHC Hq) as HEAPo.
  assert (HGo : In (gb, G, 24) (OW ++ (q, f + 32, 56) :: LB)) by (apply in_or_app; left; exact HGIN).
  assert (HDo : In (pd, D, 19) (OW ++ (q, f + 32, 56) :: LB)) by (apply in_or_app; left; exact HDIN).
  assert (HBo : In (pb, out, 128) (OW ++ (q, f + 32, 56) :: LB)) by (apply in_or_app; left; exact HBIN).
  assert (HINT : In (q, f + 32, 56) (OW ++ (q, f + 32, 56) :: LB)) by (apply in_or_app; right; left; reflexivity).
  destruct (proj1 (rw_cells_app m3 f [_; _; _; _] _) FRC) as [FRC1 FRC2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in FRC2.
  destruct (proj1 (rw_cells_app m3 (f + 32) [_] _) FRC2) as [TT FRC3]. clear FRC FRC1 FRC2 FRC3 SHC.
  (* [comment removed for export] *)
  lazymatch type of HG with rw_cells _ ?mx _ _ =>
    pose proof (proj1 (proj1 (rw_cells_app mx G [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 D)] [C8 (Z_to_bv 64 0)]) HG)) as HG3 end.
  assert (HGC : rw_cells ctasegs m3 D (gcells t (ts_ms ts))).
  { eapply rw_cells_recast; [exact HD| unfold gcells, zb8; cbn [cells_wf cell_wf app]; repeat split; exact I| | reflexivity].
    rewrite <- (genstr_gcells ts t GA). unfold zb. cbn [cells_bytes cbytes app map]. rewrite app_nil_r. reflexivity. }
  (* [comment removed for export] *)
  apply cps_from_evt'. step. apply evt_done.
  eapply (@t2t_acceptA (push AR f 1) _ _ (Z_to_bv 64 spa)) with (lo := lo) (OW := OW) (LB := (q, f + 32, 56) :: LB) (bd := (gb, G, 24)) (bs := (pd, D, 19)) (btm := (q, f + 32, 56))
        (DA := G) (GS := D) (tm := f + 32) (ms := ts_ms ts) (t := t) (tjunk := jf32);
    rewrite ?ESPA; try reflexivity.
  - exact HEAPo.
  - exact ST3.
  - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
  - unfold T2T_STACK_A, RT_STACK. clear - LO' SPAL. lia.
  - unfold USTACK_TOP. clear - TOPu SPAH. lia.
  - clear - SPA32. Z.div_mod_to_equations. lia.
  - exact MI3.
  - cbn [ar_FR push amb length]. clear - FLEN. lia.
  - cbn [ar_RT push amb]. rewrite CR1. clear - CRED. lia.
  - exact HGo.
  - cbn [blk_addr blk_size fst snd]. clear; lia.
  - uchk_open. clear - ALG. Z.div_mod_to_equations. lia.
  - exact HG3.
  - exact HDo.
  - uchk_open. clear - ALD. Z.div_mod_to_equations. lia.
  - exact HGC.
  - exact TV.
  - clear - MSR; lia.
  - clear - G1 G3 Cq3; alia.
  - intros _. split; [exact HINT|]. split; [cbn; clear; lia|]. split; [cbn; clear; lia|]. exact TT.
  - intros Σ5 m5 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F5 fc5 HEAP5 CR5 LIVE5 ST5 MI5 AG5 HTE.
    cbn [ar_RT ar_PMc ar_FR push amb] in HEAP5, CR5, LIVE5, AG5 |- *.
    rewrite (ret_pc_even 0x26fd78) by (clear; lia). unfold MallocRep.wz.
    destruct (HTE ltac:(clear - G1; lia)) as (wd & yd & TMC). clear HTE TT.
    assert (AG5' : agree_on (fun a => aclient_addr (OW ++ (q, f + 32, 56) :: LB) spa a /\ ~ (f + 32 <= a < f + 32 + 56)) m3 m5)
      by (eapply agree_on_mono; [exact AG5|]; intros a [Ha Hn]; split; [exact Ha| right; exact Hn]).
    apply (rw_cells_agree _ _ _ _ _ AG5') in LOW; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH GSZ; lia| clear - Hxa G3 CEILu LO' SPAL; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5') in HIGH; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear - Hxa G3 CEILu LO' SPAL SPAH; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5') in FR0; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| clear - Hxa G3 CEILu LO' SPAL SPAH; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5') in HG; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (gb, G, 24); split; [exact HGo| cbn; clear - Hxa; lia]| clear - Hxa OFG; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5') in HD; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pd, D, 19); split; [exact HDo| cbn; clear - Hxa; lia]| clear - Hxa OFD; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5') in HB; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pb, out, 128); split; [exact HBo| cbn; clear - Hxa; lia]| clear - Hxa OFB; lia]].
    clear HEAPo ST3 MI3 HG3 HGC HEAP1 ST1 MI1.
    ablock HEAP5 HGo ACCG OFFG2. ablock HEAP5 HDo ACCD OFFD2.
    destruct (@AH_shb (push AR f 1) _ _ _ _ HEAP5) as [SHB1 SHB2].
    pose proof (munch_refl [(spa - 16, spa + 72)]%Z m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
    assert (OFF5 : offshW [(spa - 16, spa + 72)]%Z) by (cbn [offshW]; clear - SPAL SPAH CEILu LO' Cq1 Cq2 Cq3; alia).
    assert (SEPG5 : G + 24 <= spa - 16 \/ spa + 176 <= G) by (clear - BGC CEILu LO' SPAL; unfold BnHeapA.ACEIL in BGC; lia).
    assert (SEPD5 : D + 19 <= spa - 16 \/ spa + 176 <= D) by (clear - BDC CEILu LO' SPAL; unfold BnHeapA.ACEIL in BDC; lia).
    assert (SEPT5 : f + 32 + 56 <= spa - 16 \/ spa + 176 <= f + 32) by (clear - G3 CEILu LO' SPAL; lia).
    pose proof (digit_range (ts_ms ts / 100) ltac:(clear - MSR; split; [apply Z.div_pos; lia| enough (ts_ms ts / 100 < 10) by lia; apply Z.div_lt_upper_bound; lia])) as DG1.
    pose proof (digit_range ((ts_ms ts / 10) mod 10) ltac:(clear - MSR; pose proof (Z.mod_pos_bound (ts_ms ts / 10) 10 ltac:(lia)); lia)) as DG2.
    pose proof (digit_range (ts_ms ts mod 10) ltac:(clear - MSR; pose proof (Z.mod_pos_bound (ts_ms ts) 10 ltac:(lia)); lia)) as DG3.
    unfold TM_CELLS_A in TMC.
    assert (HDC : rw_cells ctasegs m5 D (gcells t (ts_ms ts))).
    { eapply rw_cells_recast; [exact HD| unfold gcells, zb8; cbn [cells_wf cell_wf app]; repeat split; exact I| | reflexivity].
      rewrite <- (genstr_gcells ts t GA). unfold zb. cbn [cells_bytes cbytes app map]. rewrite app_nil_r. reflexivity. }
    unfold gcells, zb8, CH_DOT, CH_Z in HDC.
    (* [comment removed for export] *)
    Local Ltac fz H := lazymatch type of H with ?T => change (frozen T) in H end.
    fz OFG. fz OFD. fz OFB. fz SEPG. fz SEPG5. fz SEPD5. fz SEPT5. fz OFFG2. fz OFFD2.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    step. brc.
    step. step. step. ab_shload 4. step. step. rstep. rewrite ?zxb_z8, ?sxb_z8. if_false.
    (* [comment removed for export] *)
    try rewrite (sx32_small 19) by (clear; lia).
    (* [comment removed for export] *)
    step. try rewrite (sx32_small 24) by (clear; lia). step. step. brc. step. step. brc.
    (* [comment removed for export] *)
    step. try rewrite (zxb_lit 46) by lia. step. step. brc.
    (* [comment removed for export] *)
    step. step. step. step. try rewrite (addiw_small 19 (-15)) by lia. step. step. step. step. step.
    (* [comment removed for export] *)
    Ltac isdig_callA cv ESPA :=
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply evt_cut;
        [ eapply (ossl_ascii_isdigit_specA _ _) with (c := cv); rewrite ?ESPA;
          [ eassumption | eassumption | unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; eassumption | lia | lia | reflexivity ]
        | intros ms' PO; unfold leaf16A_post, leafA_post in PO; rewrite ?ESPA in PO; revert ms' PO; post_call ctasegs mx; rewrite ?ESPA in * ]
      end.
    step. try rewrite (zxb_lit (digit (ts_ms ts / 100))) by lia. step. isdig_callA (digit (ts_ms ts / 100)) ESPA. rewrite (isdigit_range (digit (ts_ms ts / 100))) by lia.
    step. brc. zstep. zstep. zstep. zstep. step. brc.
    step. try rewrite (zxb_lit (digit ((ts_ms ts / 10) mod 10))) by lia. step. isdig_callA (digit ((ts_ms ts / 10) mod 10)) ESPA. rewrite (isdigit_range (digit ((ts_ms ts / 10) mod 10))) by lia.
    step. brc. zstep. zstep. zstep. zstep. step. brc.
    step. try rewrite (zxb_lit (digit (ts_ms ts mod 10))) by lia. step. isdig_callA (digit (ts_ms ts mod 10)) ESPA. rewrite (isdigit_range (digit (ts_ms ts mod 10))) by lia.
    step. brc. zstep. zstep. zstep. zstep. step. brc.
    step. try rewrite (zxb_lit 90) by lia. step. isdig_callA 90 ESPA. rewrite (isdigit_false 90) by lia.
    step. brc.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. step. brc. step. step. step. brc.
    (* [comment removed for export] *)
    unfold frozen in SEPG5, SEPD5, SEPT5.
    step. rewrite (sx32_small (t_mon t - 1)) by (clear - VMO; lia). zstep.
    step. rewrite (sx32_small (t_sec t)) by (clear - VSS; lia). step. rewrite (sx32_small (t_min t)) by (clear - VMI; lia).
    step. rewrite (sx32_small (t_hour t)) by (clear - VHH; lia). step. rewrite (sx32_small (t_mday t)) by (clear - VMD; pose proof (days_in_month_le31 (t_year t) (t_mon t)); lia).
    step. rewrite (sx32_signed (t_year t - 1900)) by (clear - VY; lia).
    zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (4 * (t_mon t - 1) + A_MON_A)) ltac:(unfold A_MON_A; f_equal; rewrite ?land64, ?Z.shiftl_mul_pow2 by lia; clear - VMO; Z.to_euclidean_division_equations; lia).
    (* [comment removed for export] *)
    rzstep. setreg 10%Z (Z_to_bv 64 (t_year t)) ltac:(f_equal; first [rewrite addiw_small by (clear - VY; lia) | change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones, swrap32_mod64, swrap32_small by (clear - VY; lia)]; clear; lia).
    match goal with H : stk ctasegs _ lo _ |- _ => rename H into STc end. carve_frame 16%nat STc.
    step. zstep. zstep. step. step. step. step. step. step.
    name_mem m6.
    match goal with H : munch _ m5 m6 |- _ => rename H into MU6 end. match goal with H : wmono ctasegs m5 m6 |- _ => rename H into WM6 end.
    match goal with H : stk ctasegs m6 _ _ |- _ => rename H into ST6 end. match goal with H : mem_inv ctasegs m6 |- _ => rename H into MI6 end.
    assert (ESP6 : bv_unsigned (Z_to_bv 64 (spa + -16)) = spa + -16) by (apply unsigned_lit; clear - SPAL SPAH SPR LO' LO0; lia).
    assert (AWO6 : Forall (@aclient_write_ok (push AR f 1) (OW ++ (q, f + 32, 56) :: LB)) [(spa - 16, spa + 72)]%Z).
    { constructor; [left; cbn [fst snd]; clear - CEILu LO' SPAL SPAH TOPu GSZ; unfold BnHeapA.ACEIL, USTACK_TOP; cbn [ar_SP0 push amb]; lia| constructor]. }
    assert (HEAP6 : @BnHeapA.AHEAP (push AR f 1) Σ5 OW ((q, f + 32, 56) :: LB) m6) by (eapply (@AH_frame (push AR f 1)); [exact HEAP5| exact MU6| exact WM6| exact AWO6]).
    (* [comment removed for export] *)
    lazymatch type of HDC with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?rest) =>
      pose proof (proj2 (proj1 (rw_cells_app mx D [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14] rest) HDC)) as HF3 end.
    cbn [cells_size csize Nat.add] in HF3.
    pose proof (proj1 (proj1 (rw_cells_app m6 (D + Z.of_nat 15) [Cells.C1 (Z_to_bv 8 (digit (ts_ms ts / 100))); Cells.C1 (Z_to_bv 8 (digit ((ts_ms ts / 10) mod 10))); Cells.C1 (Z_to_bv 8 (digit (ts_ms ts mod 10)))] _) HF3)) as HF.
    pose proof (proj2 (proj1 HF)) as HFB. cbn [cells_bytes cbytes app] in HFB. replace (D + Z.of_nat 15) with (D + 15) in HFB by (clear; lia). clear HF3 HF.
    destruct (vfmtA_C16 t (ts_ms ts) TV ltac:(clear - MSR; lia)) as (o & OL & VF).
    pose proof (zdigits_le4 (t_year t) ltac:(clear - VY; lia)) as ZD. pose proof (zdigits_range (t_year t) ltac:(clear - VY; lia)) as ZR.
    apply evt_done. eapply cps_step_rt.
    { pose proof (@BIO_printf_null_cpsA_x8 (push AR f 1) PFC) as HP. cbn [ar_RT ar_PMc ar_FR push amb] in HP.
      eapply (HP _ (Z_to_bv 64 (spa + -16))) with (lo := lo) (OW := OW) (LB := (q, f + 32, 56) :: LB) (pb := pb) (out := out) (pv := pv) (nw := nw)
            (A := A_C16_A) (o := o); clear HP; rewrite ?ESP6; try reflexivity.
      - exact HEAP6.
      - exact ST6.
      - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEILu.
      - unfold BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK. clear - LO' SPAL. lia.
      - unfold USTACK_TOP. clear - TOPu SPAH. lia.
      - clear - SPA32. Z.div_mod_to_equations. lia.
      - exact MI6.
      - cbn [ar_FR push amb length]. clear - FLEN. lia.
      - cbn [ar_RT push amb]. rewrite CR5, CR1. clear - CRED. lia.
      - exact HBIN.
      - unfold bio_null_cells, bio_cells, MallocRep.wz. exact HB.
      - exact NW.
      - exact VF.
      - clear - OL ZD ZR. lia.
      - exact FR.
      - cbn [vargsA_okx vargA_okx vhd_cov tl vcovs]. change (vcovs FMT_C16 _) with [None; None; None; None; None; None; Some 3; None]. cbn [vhd_cov tl].
        split; [left; apply mon_vargA; clear - VMO; lia|].
        split; [cbn; rewrite unsigned_lit by (clear - VMD; pose proof (days_in_month_le31 (t_year t) (t_mon t)); lia); clear - VMD; pose proof (days_in_month_le31 (t_year t) (t_mon t)); split; [lia| reflexivity]|].
        split; [cbn; rewrite unsigned_lit by (clear - VHH; lia); clear - VHH; split; [lia| reflexivity]|].
        split; [cbn; rewrite unsigned_lit by (clear - VMI; lia); clear - VMI; split; [lia| reflexivity]|].
        split; [cbn; rewrite unsigned_lit by (clear - VSS; lia); clear - VSS; split; [lia| reflexivity]|].
        split; [cbn; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|].
        split.
        { right. exists 3. split; [reflexivity|]. change (zlength (dec3 (ts_ms ts))) with 3. split; [clear; lia|]. split; [clear - DG1 DG2 DG3; unfold dec3; repeat constructor; lia|]. split; [clear; lia|].
          exists (pd, D, 19). rewrite unsigned_lit by (clear - BD0 BDC Cq3; alia). split; [exact HDo|]. split; [cbn; clear; lia|]. split; [cbn; clear; lia|]. exact HFB. }
        split; [| exact I]. cbn. rewrite unsigned_lit by (clear - VY; lia). clear - VY. split; [lia| reflexivity]. }
    intros Σ7 msP PO7 LIVE7. unfold bio_printf_null_post in PO7. rewrite ?ESP6 in PO7.
    destruct PO7 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F7 & fc7 & m7 & -> & MI7 & ST7 & AP7 & HEAP7 & _ & CR7 & HB7).
    rewrite (ret_pc_even 0x270098) by (clear; lia). unfold MallocRep.wz. cbn [ar_PMc ar_RT push amb] in HEAP7, CR7, LIVE7 |- *.
    unfold apres_ex, BIO_SIZE in AP7.
    apply (rw_cells_agree _ _ _ _ _ AP7) in LOW; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH GSZ; lia| split; [clear - Hxa BBC CEILu LO' SPAL; unfold BnHeapA.ACEIL in BBC; lia| exact I]]].
    apply (rw_cells_agree _ _ _ _ _ AP7) in HIGH; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| split; [clear - Hxa BBC CEILu LO' SPAL SPAH; unfold BnHeapA.ACEIL in BBC; lia| exact I]]].
    apply (rw_cells_agree _ _ _ _ _ AP7) in FR0; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| split; [clear - Hxa BBC CEILu LO' SPAL SPAH; unfold BnHeapA.ACEIL in BBC; lia| exact I]]].
    apply (rw_cells_agree _ _ _ _ _ AP7) in FR; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH SPAL; lia| split; [clear - Hxa BBC CEILu LO' SPAL SPAH; unfold BnHeapA.ACEIL in BBC; lia| exact I]]].
    pose proof HEAP7 as HEAP7c.
    eapply (@frame_obj_close (push AR f 1)) in HEAP7c; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
    pose proof (munch_refl [(spa - 16, spa + 72)]%Z m7) as MU7. pose proof (wmono_refl ctasegs m7) as WM7.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    release_frame FR ST7 spa. step. step.
    zstep. setreg 10%Z (Z_to_bv 64 1) ltac:(rewrite sgt0_lit by (clear - OL ZD ZR; lia); rewrite (proj2 (Z.ltb_lt 0 (zlength o))) by (clear - OL ZD ZR; lia); reflexivity).
    apply evt_done.
    change (Z_to_bv 64 0x26ff48) with (wz TPX_EXIT).
    eapply (tpx_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAP7c| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| first [exact ST7| rewrite <- ?ESPA; exact ST7]| exact CEIL| clear - LO' SPAL; lia
      | rewrite ESP; unfold USTACK_TOP; clear - TOPu; lia| rewrite ESP; exact SPAL| rewrite ESP; exact SPAH| rewrite ESP; exact GSZ| exact SAVJ| exact MI7
      | first [exact LOW| eapply (rw_cells_recast m7 spa _ _ LOW); [| reflexivity| reflexivity]; pose proof (proj1 (proj1 LOW)) as WF; cbn in WF; cbn; repeat split; try reflexivity;
              repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption]
      | rewrite ESP; exact HIGH| reflexivity|].
    intros Σ8 m8 x11' HEAP8 CR8 LIVE8 ST8 MI8 AG8.
    assert (ESP8 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; clear - SPR LO' LO0; lia).
    pose proof (@eq_ind _ _ (fun z => stk ctasegs m8 lo z) ST8 _ ESP8) as ST9. cbv beta in ST9. clear ST8. rename ST9 into ST8.
    apply (rw_cells_agree _ _ _ _ _ AG8) in FR0; [| intros xa Hxa; cbn in Hxa; left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG8) in HB7; [| intros xa Hxa; unfold bio_null_cells, bio_cells in Hxa; cbn in Hxa; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Hxa; lia]].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m8) as MU8. pose proof (wmono_refl ctasegs m8) as WM8.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    rewrite (ret_pc_even 0x26fc34) by (clear; lia).
    zstep. setreg 10%Z (Z_to_bv 64 1) ltac:(reflexivity).
    step. step. release_frame FR0 ST8 (bv_unsigned sp). step. step.
    apply evt_done.
    eapply (K Σ8 m8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (zlength o)); [clear - OL ZD ZR; lia| exact HEAP8| rewrite CR8; clear - CR7 CR5 CR1; lia| rewrite LIVE8, LIVE7, LIVE5; exact LIVE1| assumption| assumption| |].
    + (* [comment removed for export] *)
      unfold apres_ex. unfold frozen in OFG, OFD, OFB.
      assert (STKW : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a ->
                outside [(bv_unsigned sp - 32, bv_unsigned sp)]%Z a /\ outside [(spa - 16, spa + 72)]%Z a /\ ~ (f + 32 <= a < f + 32 + 56)).
      { intros a Ha. cbn [outside fst snd].
        destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
        - clear - Ha SPAH SPAL G3 CEILu LO'. repeat split; try exact I; lia.
        - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
          destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' SPAL Cq1 G4; unfold BnHeapA.ACEIL in *; repeat split; try exact I; lia.
        - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O.
          destruct b as [[bq bA] bn]; cbn [blk_addr blk_size fst snd] in Hr, O, B3'. clear - Hr B3' O CEILu LO' SPAL. unfold BnHeapA.ACEIL in *. repeat split; try exact I; lia. }
      assert (LIFT : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> forall lv, lv <= bv_unsigned sp -> aclient_addr (OW ++ (q, f + 32, 56) :: LB) lv a).
      { intros a Ha lv Hlv. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha Hlv; lia| right; left; exact Ha| right; right].
        exists b. split; [| exact Hr]. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]. }
      eapply agree_on_trans; [eapply agree_on_mono; [exact AG3| intros a [Ha _]; exact Ha]|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AG5| intros a [Ha _]; split; [exact (LIFT a Ha spa ltac:(clear - SPAH; lia))| right; exact (proj2 (proj2 (STKW a Ha)))]]|].
      eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU6)| intros a [Ha _]; exact (proj1 (proj2 (STKW a Ha)))]|].
      eapply agree_on_trans; [eapply agree_on_mono; [exact AP7| intros a [Ha Hn]; split; [exact (LIFT a Ha (spa + -16) ltac:(clear - SPAH; lia))| exact Hn]]|].
      eapply agree_on_mono; [exact AG8|]. intros a [Ha _].
      destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
    + exact HB7.
Qed.

End WithRT.
