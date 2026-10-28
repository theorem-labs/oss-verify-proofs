(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma word_range : forall w : word, 0 <= bv_unsigned w < 2^64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. cbn in R. lia. Qed.
Lemma byte_eq_of_unsigned : forall (b : byte) z, bv_unsigned b = z -> b = Z_to_bv 8 z.
Proof. intros b z E. subst z. symmetry. apply (bitvector.definitions.Z_to_bv_bv_unsigned 8). Qed.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition ACM_RA : Z := R_CRYPTO_malloc_malloc.   (* [comment removed for export] *)
  Definition ACM_A2 : Z := 0x5e88a8.                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition cm_frame (j : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
    [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Ltac prep_statics IM GM :=
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_aligned_alloc,
      P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition acm1_post (sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
      (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 j,
      ms' = MS (mkR (Z_to_bv 64 ACM_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a2
                   (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 ACM_A2) (Z_to_bv 64 P_CRYPTO_malloc) a4 a5 a6 a7
                   a1 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AMALLOC_STUB) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp); (A_mem_inited, A_mem_inited + 1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells asegs m1 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra)
      /\ MEMFLAG m1 1 /\ IMPL_mem m1 /\ GOT_mem m1.

  Lemma acm_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (n v lo : Z),
      1 <= n <= 2^28 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      evt asegs (acm1_post sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HN ST CEIL LO MI MF IM GM. acb.
    unfold P_CRYPTO_malloc in *. prep_statics IM GM.
    destruct IM as (IM1 & IM2 & IM3).
    destruct MF as (fb & MF & FBV & V01). unfold A_mem_inited in MF.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (0xbdcf80, 0xbdcf80 + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    do 15 step. if_true. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step.
    assert (FIN : forall m1,
      munch [(bv_unsigned sp + -48, bv_unsigned sp); (0xbdcf80, 0xbdcf80 + 1)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
      stk asegs m1 lo (bv_unsigned sp + -48) ->
      rw_cells asegs m1 (bv_unsigned sp + -48) (cm_frame (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 junk))))) s3 s2 s1 s0 ra) ->
      rw_cells asegs m1 0xbdcf80 [C1 (Z_to_bv 8 1)] ->
      rw_cells asegs m1 0x5ed1a0 [C8 (Z_to_bv 64 0x1f0880)] -> rw_cells asegs m1 0x5ed1c0 [C8 (Z_to_bv 64 0x1f0c94)] -> rw_cells asegs m1 0x5ed1e0 [C8 (Z_to_bv 64 0x1f0da4)] ->
      rw_cells asegs m1 0x5e8e30 [C8 (Z_to_bv 64 0x1f0880); C8 (Z_to_bv 64 0x1f09a0); C8 (Z_to_bv 64 0x1f0c94); C8 (Z_to_bv 64 0x1f0da4)] ->
      evt asegs (acm1_post sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc n lo m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a2 (Z_to_bv 64 0xbdc8dc) (Z_to_bv 64 1)
                 (Z_to_bv 64 ACM_A2) (Z_to_bv 64 0x1f0880) a4 a5 a6 a7 a1 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f08f0) fc None m1 (seg_rom asegs))).
    { intros m1 MU1 WM1 MI1 ST1 FR1 MF1 IM1' IM2' IM3' GM1. clear MU WM MI ST FR MF IM1 IM2 IM3 GM. unfold ACM_A2.
      step. step. unfold acm1_post, ACM_RA, ACM_A2, R_CRYPTO_malloc_malloc, AMALLOC_STUB, A_mem_inited. finish; [exact FR1| |].
      - exists (Z_to_bv 8 1). split; [exact MF1| split; [reflexivity| lia]].
      - unfold IMPL_mem, A_malloc_impl, A_realloc_impl, A_free_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz. auto. }
    cbv delta [mkR] in FIN. unfold ACM_A2 in FIN.
    destruct V01 as [-> | ->].
    - replace fb with (b8 0) in MF by (symmetry; exact (byte_eq_of_unsigned fb 0 FBV)).
      st1. unfold wz. step. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. } clear K1.
      step. st1.
      eapply FIN; eassumption.
    - replace fb with (b8 1) in MF by (symmetry; exact (byte_eq_of_unsigned fb 1 FBV)).
      st1. unfold wz. step.
      try (if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; lia]; clear K1).
      eapply FIN; first [eassumption| exact MF].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma acm_seg2 :
    forall (sp gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (j : list byte),
      0 < A < 2^64 ->
      rw_cells asegs m (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (ret_pc ra) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ACM_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ACM_RA)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HA FR MI. unfold ACM_RA, R_CRYPTO_malloc_malloc.
    replace (ret_pc (Z_to_bv 64 0x1f08f8)) with (Z_to_bv 64 0x1f08f8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold cm_frame in FR.
    step. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 7 step. apply evt_done. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma acmalloc_spec : cmalloc_stmt H.
  Proof.
    unfold cmalloc_stmt, cmalloc_stmt_at. intros until CH.
    intros VIS A0 HN HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM.
    unfold CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK in LO. acb. subst a0. subst tp.
    rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. pose proof (word_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply acm_seg1; try eassumption; lia|].
    intros msF1 mo1 KREL1 MP1 (m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & MF1 & IM1 & GM1).
    unfold A_mem_inited in MU1.
    (* [comment removed for export] *)
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -48, bv_unsigned sp); (0xbdcf80, 0xbdcf80 + 1)]).
    { constructor; [left; cbn; lia|]. constructor; [| constructor]. right; left. unfold aimg_client_w, ATLS_PRIV_LO, ATP. cbn. lia. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -48, bv_unsigned sp); (0xbdcf80, 0xbdcf80 + 1)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
      constructor; [| constructor].
      (* [comment removed for export] *)
      apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AF_DCO_CELL, AVERBOSITY_CELL,
        AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
    { eapply (rw_cells_transport asegs _ m m1); [exact ERR| exact MU1| exact WM1|]. unfold ATP. cbn. lia. }
    (* [comment removed for export] *)
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (ah_chain_ext H HH); [exact CHN|]. intros fp' ra' a Hin Ha.
      destruct (ah_chain_range H HH _ _ _ _ _ CHN Hin) as (R1 & _ & _). specialize (CHS _ _ Hin).
      rewrite <- (Z_to_bv_bv_unsigned 64 (wa a)) || idtac.
      unfold wa. apply MU1. cbn. rewrite unsigned_lit by lia. lia. }
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      unfold cm_frame in FR1.
      change ([CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 j; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR1.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR1. destruct FR1 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -48 + 32) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    (* [comment removed for export] *)
    pose proof (ah_malloc H HH) as MA. unfold malloc_stmt, malloc_stmt_at in MA.
    eapply (ah_seq H HH).
    { eapply MA with (lo := lo) (B := B) (LB := LB) (s := s) (n := n) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS1| ..];
        rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold AMALLOC_STACK; lia).
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_alloc_ok _ _ _ _ => eapply (ah_alloc H HH); [exact HP1| lia| lia| lia]
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ _ => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ mod 16 = 0 => rewrite <- Zminus_mod_idemp_l; rewrite <- Zminus_mod_idemp_l in SP16 || idtac; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia;
                                rewrite Zminus_mod, SP16; reflexivity
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CH1
           | |- trace_ok _ _ _ => cbn [map snd]; exact (pf_ok_site _ _ _ _ _ _ PF (or_introl eq_refl))
           end. }
    intros [msF2 mo2] PO. unfold malloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' &
                    VIS2 & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & BR & HEAP2 & BLK & ADDR & AC2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, HPRES by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7).
    apply (apres_rw_cells H _ _ _ _ _ _ HPRES) in FR1; [| left; cbn; lia].
    (* [comment removed for export] *)
    eapply (ahh_evt H HH); [exact KREL2| exact VIS2| eapply acm_seg2; [lia| exact FR1| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3.
    unfold cmalloc_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, junk, p, s'.
    split; [exact VIS3|]. split; [exact KREL3|]. split; [eapply (ah_mpres_trans H HH); [| exact MP3]; eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI2|]. split; [exact AC2|].
    split. { unfold cm_frame in FR1. release_frame FR1 ST2 (bv_unsigned sp). exact ST2. }
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR2|]. split; [exact AUX2|].
    split.
    { eapply xpres_trans.
      - eapply (xpres_of_munch H s LB _ memflag_foot _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|].
        constructor; [left; cbn; lia|]. constructor; [right; cbn; intros a Ha; unfold memflag_foot, A_mem_inited; cbn; lia| constructor].
      - eapply (xpres_weaken H LB LB _ _ memflag_foot); [apply xpres_of_apres; exact HPRES| lia| auto| auto]. }
    split; [exact BR|]. split; [exact HEAP2|]. split; [exact BLK|]. split; [exact ADDR|].
    split.
    { destruct MF1 as (fb1 & MF1 & FB1 & _). exists fb1. split; [| split; [exact FB1| lia]].
      eapply (apres_rw_cells H); [exact HPRES| exact MF1|]. right; left. unfold A_mem_inited, aimg_client. cbn. lia. }
    split.
    { destruct IM1 as (I1 & I2 & I3). unfold IMPL_mem.
      repeat split; (eapply (apres_rw_cells H); [exact HPRES| eassumption|]); right; left; unfold A_malloc_impl, A_realloc_impl, A_free_impl, aimg_client; cbn; lia. }
    split.
    { eapply (apres_rw_cells H); [exact HPRES| exact GM1|]. right; left. unfold A_got_CRYPTO_malloc, aimg_client. cbn. lia. }
    exact AL2.
  Qed.
End W.
