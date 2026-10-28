(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C8 ECH_AKit ECH_AsKit ECH_AC1_zalloc ECH_AC1_free.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition AENC_FILE : Z := 0xc0e58.     (* [comment removed for export] *)
Definition AEN_T1 : Z := 0x1f06d0.       (* [comment removed for export] *)
Definition AEF_T1 : Z := 0x1f0700.       (* [comment removed for export] *)

(* [comment removed for export] *)
Section K4.
  Context {HCEIL : HeapCeil}.
  Lemma accessible_read4 : forall m a, accessible m a 4 -> a mod 8 <= 4 ->
    exists v, 0 <= v < 8 /\ (v = 0 \/ a mod 8 + 4 <= v) /\ ov_read_bytes asegs m (wa (sh a)) 1 = Some [b8 v].
  Proof.
    intros m a ACC AM. pose proof ACC as (A0 & A1 & AC).
    destruct (accessible_read1 m (a + 3) ltac:(eapply accessible_sub; [exact ACC| lia| lia| lia])) as (v & V1 & V2 & RD).
    exists v. split; [exact V1|]. split.
    - destruct V2 as [V2|V2]; [left; exact V2| right]. clear - V2 AM A0. Z.div_mod_to_equations. lia.
    - replace (sh a) with (sh (a + 3)); [exact RD|]. unfold sh. clear - AM A0. Z.div_mod_to_equations. nia.
  Qed.
  Lemma ck4_blt_true : forall a v, 0 <= a -> 0 <= v < 8 -> a mod 8 + 4 <= v ->
    bv_lts (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 a)) 7 + 3)) (Z_to_bv 64 v) = true.
  Proof.
    intros a v Ha Hv Hav. rewrite ck1_land7_of_word by exact Ha.
    unfold bv_lts. rewrite !Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 64 / 2) with (2^63). change (2 ^ Z.of_N 64) with (2^64).
    rewrite (Z.mod_small (a mod 8 + 3 + 2^63)) by (Z.div_mod_to_equations; lia). rewrite (Z.mod_small (v + 2^63)) by lia.
    destruct (Z.ltb_spec (a mod 8 + 3 + 2 ^ 63 - 2 ^ 63) (v + 2 ^ 63 - 2 ^ 63)); [reflexivity| exfalso; Z.div_mod_to_equations; lia].
  Qed.
End K4.
(* [comment removed for export] *)
Ltac ck4_load ACC a v V1 V2 Ha :=
  let ACW := fresh "ACW" in let RD := fresh "RD" in let SXV := fresh "SXV" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (ACW : accessible mc a 4) by (eapply accessible_sub; [exact ACC| lia| lia| lia]) end;
  assert (Ha : 0 <= a) by lia;
  destruct (accessible_read4 _ _ ACW ltac:(Z.div_mod_to_equations; lia)) as (v & V1 & V2 & RD);
  rewrite <- (sh_shiftr a), ASHADOW_BASE_val in RD by exact Ha;
  replace (wa (Z.shiftr a 3 + 2147450880)) with (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) in RD by (symmetry; apply wa_of_Z_to_bv; lia);
  step; clear RD ACW;
  assert (SXV : sxb (b8 v) = Z_to_bv 64 v) by (unfold sxb; rewrite b8_signed_small by lia; reflexivity); rewrite SXV; clear SXV.
(* [comment removed for export] *)
Ltac ck4_branch_blt a v V1 V2 Ha K :=
  let Ev := fresh "Ev" in let Nv := fresh "Nv" in let VV := fresh "VV" in
  step; destruct (Z.eq_dec v 0) as [Ev|Nv];
  [ if_false_by (ck1_bnez_false v Ev); apply K
  | if_true_by (ck1_bnez_true v V1 Nv); destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|];
    step; step; step; if_true_by (ck4_blt_true a v Ha V1 VV); apply K ].

Section S.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma rw_cells_recut : forall m A cs cs',
    rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
  Proof.
    intros m A cs cs' [[WF B] W] WF' E. split; [split; [exact WF'| rewrite E; exact B]|].
    rewrite <- (cells_bytes_length cs' WF'), E, (cells_bytes_length cs WF). exact W.
  Qed.
  Lemma rw_cells_as_CB : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
  Proof.
    intros m A cs RC. pose proof RC as [[WF _] _]. eapply rw_cells_recut; [exact RC| |].
    - cbn. split; [apply cells_bytes_length; exact WF| exact I].
    - cbn. rewrite app_nil_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma aen_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 AEN_T1) t2 s0 s1 (Z_to_bv 64 92) (Z_to_bv 64 AENC_FILE) (Z_to_bv 64 112) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_ENCODE_CTX_new) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros ST LO MI. acb. unfold P_EVP_ENCODE_CTX_new, P_CRYPTO_zalloc, AENC_FILE, AEN_T1.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 step. do 4 step. do 3 step. step. step.
    release_frame FR ST (bv_unsigned sp). finish. all: match goal with |- ?G => idtac "AEN1:" G end.
  Qed.

  (* [comment removed for export] *)
  Lemma aef_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 AEF_T1) t2 s0 s1 a0 (Z_to_bv 64 AENC_FILE) (Z_to_bv 64 117) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_ENCODE_CTX_free) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros ST LO MI. acb. unfold P_EVP_ENCODE_CTX_free, P_CRYPTO_free, AENC_FILE, AEF_T1.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 4 step. do 3 step. do 3 step. step. step.
    release_frame FR ST (bv_unsigned sp). finish. all: match goal with |- ?G => idtac "AEF1:" G end.
  Qed.
End S.
Section S2.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma adi_seg :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (old : list byte),
      rw_cells asegs m a [CB 92 old] -> 0 < a -> a mod 16 = 0 -> a + 92 <= aceil -> aceil <= lo -> accessible m a 92 -> aapp a 92 -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists m1 a1' a2' a3' a4',
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (a + 88)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp); (a, a + 92)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp)
          /\ rw_cells asegs m1 a [C4 (wz 0); CB 80 (firstn 80 (skipn 4 old)); C4 (wz 0); C4 (wz 0)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeInit) fc None m (seg_rom asegs)).
  Proof.
    intros until old. intros BLK POS AL BL CEIL ACC0 AP AC ST LO MI RAE. unfold P_EVP_DecodeInit.
    pose proof (rw_cells_bound _ _ _ _ BLK) as HB. cbn [cells_size csize Nat.add length] in HB.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ACONST_shbase _ AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof (aapp_not_shadowland _ _ AP) as NS1.
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp); (a, a + 92)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 92)) in ACC'.
    carve_frame 16%nat ST.
    do 4 step.
    (* [comment removed for export] *)
    step. ub_dead. step. ubal_by AL. step. if_lit. step. step. step.
    Local Ltac reacc ACC' MU NS1 :=
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        let ACC := fresh "ACC" in
        assert (ACC : accessible mx _ 92) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|];
          apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia| apply Forall_cons; [cbn [fst snd]; exact NS1| apply Forall_nil]]) end.
    (* [comment removed for export] *)
    reacc ACC' MU NS1. zstep. zstep. ck8_check ACC a. clear ACC.
    st1.
    (* [comment removed for export] *)
    reacc ACC' MU NS1. zstep. zstep. zstep. ck8_check ACC (a + 84). clear ACC.
    st1.
    (* [comment removed for export] *)
    reacc ACC' MU NS1. zstep. zstep. zstep.
    ck4_load ACC (a + 88) v V1 V2 Ha.
    step. destruct (Z.eq_dec v 0) as [Ev|Nv].
    - if_false_by (ck1_bnez_false v Ev).
      st1. do 4 step. release_frame FR ST (bv_unsigned sp). finish. all: match goal with |- ?G => idtac "DIF:" G end.
    - if_true_by (ck1_bnez_true v V1 Nv). destruct V2 as [VV|VV]; [exfalso; exact (Nv VV)|].
      step. step. step. if_true_by (ck4_blt_true (a + 88) v Ha V1 VV).
      st1. do 4 step. release_frame FR ST (bv_unsigned sp). finish. all: match goal with |- ?G => idtac "DIS:" G end.
  Qed.
End S2.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma aencnew_spec : encnew_stmt H.
  Proof.
    unfold encnew_stmt. intros until CH.
    intros VIS HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM RAE.
    unfold ENCNEW_STACK, FR_EVP_ENCODE_CTX_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK, ENCCTX_SIZE in *.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply aen_seg1; [exact ST| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 v) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (XP1 : xpres H LB (bv_unsigned sp) memflag_foot m m1).
    { eapply (xpres_of_munch H s LB _ memflag_foot _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    (* [comment removed for export] *)
    assert (CH1 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_mono H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 92) (size := 1) (CH := CH);
        [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK; lia).
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ mod 16 = 0 => exact SP16
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CH1
           | |- forall fp' ra', In _ _ -> _ => exact CHS
           | |- pf_ok _ _ _ _ => exact PF
           | |- _ <= as_AL _ _ => exact HAL
           | |- MEMFLAG _ _ => exact MF1
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- ?G => idtac "LEFT:" G
           end. }
    intros [msF2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & ADDR & MF2 & IM2 & GM2 & AL2).
    change (92 * 1) with 92 in BR, HEAP2, BLK, ADDR, AL2.
    unfold encnew_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, p, s'.
    split; [exact VIS2|]. split; [exact KREL2|]. split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR2|]. split; [exact AUX2|].
    split; [eapply xpres_trans; [exact XP1| exact XP2]|].
    split; [exact HEAP2|].
    split.
    { unfold ENCCTX. exists (zeros 80), 0.
      split; [reflexivity|]. split; [reflexivity|].
      split. { eapply rw_cells_recut; [exact BLK| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. }
      split; [lia|]. split; [left; reflexivity|]. split; [exact BR|].
      unfold du_inv. split; [constructor| cbn; lia]. }
    split; [exact ADDR|]. split; [exact MF2|]. split; [exact IM2|]. split; [exact GM2|]. exact AL2.
  Qed.

  Lemma aencfree_spec : encfree_stmt H.
  Proof.
    unfold encfree_stmt. intros until CH.
    intros VIS A0 EO ADDR HP KREL AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL IM GM RAE.
    unfold ENCFREE_STACK, FR_EVP_ENCODE_CTX_free, CFREE_STACK, AFREE_STACK, ENCCTX_SIZE in *.
    acb. subst a0. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct EO as (raw & line & L80 & FD & EC & LR & EIN & EBR & DI).
    pose proof EBR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4.
    pose proof (aapp_bounds a 92 BR7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply aef_seg1; [exact ST| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (EC1 : rw_cells asegs m1 a [C4 (wz (zlength d)); CB 80 raw; C4 (wz line); C4 (wz 0)]).
    { eapply rw_cells_transport; [exact EC| exact MU1| exact WM1|]. cbn [cells_size csize Nat.add length disjoint_from]. split; [lia| exact I]. }
    assert (ADDR1 : addressable m1 a 92).
    { eapply addressable_transport; [exact ADDR| exact MU1| exact WM1|].
      pose proof (sh_below_aceil (a + 92 + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
      unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. cbn. Z.div_mod_to_equations. lia. }
    assert (CH1 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    pose proof (rw_cells_as_CB _ _ _ EC1) as BCB. cbn [cells_size csize Nat.add] in BCB. change 92%nat with (Z.to_nat 92) in BCB.
    eapply (ah_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (A := a) (n := 92) (CH := CH) (errv := errv) (bs := cells_bytes [C4 (wz (zlength d)); CB 80 raw; C4 (wz line); C4 (wz 0)]);
        [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CFREE_STACK, AFREE_STACK; lia).
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- In _ _ => exact EIN
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- rw_cells _ _ _ [CB _ _] => exact BCB
           | |- addressable _ _ _ => exact ADDR1
           | |- mem_inv _ _ => exact MI1
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CH1
           | |- forall fp' ra', In _ _ -> _ => exact CHS
           | |- pf_ok _ _ _ _ => exact PF
           | |- _ <= as_AL _ _ => exact HAL
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- ?G => idtac "LEFT:" G
           end. }
    intros [msF2 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2 & AL2).
    unfold encfree_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv, s'.
    split; [exact VIS2|]. split; [exact KREL2|]. split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR2|]. split; [exact AUX2|].
    assert (SUB : forall b, In b (as_lb_remove H p LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    split.
    { eapply xpres_trans; [| exact XP2].
      eapply (xpres_weaken H LB (as_lb_remove H p LB) (bv_unsigned sp) (bv_unsigned sp) [] []);
        [eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|] | lia | exact SUB | auto].
      constructor; [left; cbn; lia| constructor]. }
    split; [exact HEAP2|]. split; [exact IM2|]. split; [exact GM2|]. exact AL2.
  Qed.
End W.

(* [comment removed for export] *)
Section P.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma adecinit_spec : decinit_stmt H.
  Proof.
    unfold decinit_stmt. intros until old. intros A0 BLK EIN BR BL ACC AC ST CEIL LO MI RAE. subst a0.
    unfold DECINIT_STACK, FR_EVP_DecodeInit in LO. unfold ENCCTX_SIZE in *.
    acb. pose proof (aword_range sp) as SPR.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7).
    eapply evt_mono; [eapply adi_seg with (lo := lo); [exact BLK| exact BR1| lia| exact BR5| exact CEIL| exact ACC| exact BR7| exact AC| exact ST| exact LO| exact MI| exact RAE]|].
    intros ms' (m1 & a1' & a2' & a3' & a4' & -> & MU1 & WM1 & MI1 & ST1 & BLK1). unfold c8_post.
    exists t0, t1, t2, (Z_to_bv 64 (a + 88)), a1', a2', a3', a4', a5, a6, a7, t3, t4, t5, t6, m1.
    split; [reflexivity|]. split; [reflexivity|].
    split. { unfold ENCCTX_foot, ENCCTX_SIZE. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia. }
    split; [exact WM1|]. split; [exact MI1|].
    split. { eapply ACONST_frame; [exact AC| exact MU1| exact WM1|].
             apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
             apply Forall_cons; [eapply aconst_ok_aapp; [exact BR7| cbn; lia| cbn; lia]| apply Forall_nil]. }
    split; [exact ST1|].
    split; [| exact I].
    unfold ENCCTX. exists (firstn 80 (skipn 4 old)), 0.
    assert (L92 : length old = 92%nat) by (destruct BLK as [[WF _] _]; cbn in WF; destruct WF as [L _]; exact L).
    split; [rewrite length_firstn, length_skipn, L92; reflexivity|]. split; [reflexivity|].
    split; [exact BLK1|]. split; [lia|]. split; [exact EIN|]. split; [exact BR|].
    unfold du_inv. split; [constructor| cbn; lia].
  Qed.
End P.
