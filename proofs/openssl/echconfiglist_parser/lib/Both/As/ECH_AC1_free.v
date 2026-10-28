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

Section S.
  Context {HCEIL : HeapCeil}.

  Definition ACF_A4 : Z := 0x5e8db8.          (* [comment removed for export] *)

  Local Ltac prep_statics IM GM :=
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_aligned_alloc,
      P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.

  (* [comment removed for export] *)
  Definition acf1_post (ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 P_CRYPTO_free) t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P_CRYPTO_free) (Z_to_bv 64 ACF_A4) a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AFREE_STUB) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp) /\ IMPL_mem m1 /\ GOT_mem m1.

  Lemma acf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m -> IMPL_mem m -> GOT_mem m ->
      evt asegs (acf1_post ra sp gp tp t0 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI IM GM. acb. unfold P_CRYPTO_free in *. prep_statics IM GM.
    destruct IM as (IM1 & IM2 & IM3).
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 9 step. if_true. do 4 step.
    release_frame FR ST (bv_unsigned sp).
    unfold acf1_post, ACF_A4, AFREE_STUB. finish.
    unfold IMPL_mem, A_malloc_impl, A_realloc_impl, A_free_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz. auto.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma acfree_spec : cfree_stmt H.
  Proof.
    unfold cfree_stmt. intros until bs.
    intros VIS A0 HP KREL HIN AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL CELLS ADDR IM GM.
    unfold CFREE_STACK, AFREE_STACK in LO. acb. subst tp. subst a0.
    rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. pose proof (word_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ah_blocks H HH _ _ _ _ HP HIN) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *. unfold AIMG_TOP in B4.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply acf_seg1; try eassumption; lia|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & IM1 & GM1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
    { eapply (rw_cells_transport asegs _ m m1); [exact ERR| exact MU1| exact WM1|]. unfold ATP. cbn. lia. }
    (* [comment removed for export] *)
    assert (CELLS1 : rw_cells asegs m1 A [CB (Z.to_nat n) bs]).
    { eapply (rw_cells_transport asegs _ m m1); [exact CELLS| exact MU1| exact WM1|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. lia. }
    assert (ADDR1 : addressable m1 A n).
    { eapply addressable_transport; [exact ADDR| exact MU1| exact WM1|].
      pose proof (sh_below_aceil (A + n + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
      unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. cbn. Z.div_mod_to_equations. lia. }
    destruct ADDR1 as [Hn0 SH1].
    (* [comment removed for export] *)
    assert (CH1 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (ah_chain_ext H HH); [exact CHN|]. intros fp' ra' a Hin Ha.
      destruct (ah_chain_range H HH _ _ _ _ _ CHN Hin) as (R1 & _ & _). specialize (CHS _ _ Hin).
      rewrite <- (Z_to_bv_bv_unsigned 64 (wa a)) || idtac.
      unfold wa. apply MU1. cbn. rewrite unsigned_lit by lia. lia. }
    (* [comment removed for export] *)
    pose proof (ah_free H HH) as FRE. unfold free_stmt, free_stmt_at in FRE.
    eapply (ah_seq H HH).
    { eapply FRE with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (A := A) (n := n) (CH := CH) (bs := bs) (sbs := shadow_of n);
        [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold AFREE_STACK; lia).
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- In _ _ => exact HIN
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- rw_cells _ _ _ [CB _ _] => exact CELLS1
           | |- SHAD _ _ _ => exact SH1
           | |- Z.of_nat (length (shadow_of ?k)) = nsh ?k => apply shadow_of_length; lia
           | |- mem_inv _ _ => exact MI1
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CH1
           | |- trace_ok _ _ _ => exact (pf_ok_site _ _ _ _ _ _ PF (or_introl eq_refl))
           | |- _ <= as_AL _ _ => exact HAL
           | |- ?G => idtac "LEFT:" G
           end. }
    intros [msF2 mo2] PO. unfold free_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                    VIS2 & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & HEAP2 & AC2 & AL2).
    apply (ah_done H HH).
    unfold cfree_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s'.
    split; [exact VIS2|]. split; [exact KREL2|]. split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR2|]. split; [exact AUX2|].
    assert (SUB : forall b, In b (as_lb_remove H p LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    split.
    { eapply xpres_trans.
      - eapply (xpres_weaken H LB (as_lb_remove H p LB) (bv_unsigned sp) (bv_unsigned sp) [] []);
          [eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|] | lia | exact SUB | auto].
        constructor; [left; cbn; lia| constructor].
      - apply xpres_of_apres. exact HPRES. }
    split; [exact HEAP2|].
    split.
    { destruct IM1 as (I1 & I2 & I3). unfold IMPL_mem.
      repeat split; (eapply (apres_rw_cells H); [exact HPRES| eassumption|]); right; left; unfold A_malloc_impl, A_realloc_impl, A_free_impl, aimg_client; cbn; lia. }
    split.
    { eapply (apres_rw_cells H); [exact HPRES| exact GM1|]. right; left. unfold A_got_CRYPTO_malloc, aimg_client. cbn. lia. }
    exact AL2.
  Qed.

  Lemma acfree_null_spec : cfree_null_stmt H.
  Proof.
    unfold cfree_null_stmt. intros until CH.
    intros VIS HP KREL AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS HAL IM GM.
    unfold CFREE_STACK, AFREE_STACK in LO. acb. subst tp.
    rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. pose proof (word_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply acf_seg1; try eassumption; lia|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & IM1 & GM1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -16, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]).
    { eapply (rw_cells_transport asegs _ m m1); [exact ERR| exact MU1| exact WM1|]. unfold ATP. cbn. lia. }
    assert (CH1 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (ah_chain_ext H HH); [exact CHN|]. intros fp' ra' a Hin Ha.
      destruct (ah_chain_range H HH _ _ _ _ _ CHN Hin) as (R1 & _ & _). specialize (CHS _ _ Hin).
      rewrite <- (Z_to_bv_bv_unsigned 64 (wa a)) || idtac.
      unfold wa. apply MU1. cbn. rewrite unsigned_lit by lia. lia. }
    pose proof (ah_free_null H HH) as FRE. unfold free_null_stmt_at in FRE.
    eapply (ah_seq H HH).
    { eapply FRE with (lo := lo) (B := B) (LB := LB) (s := s) (CH := CH); [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold AFREE_STACK; lia).
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ _ => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CH1
           | |- _ <= as_AL _ _ => exact HAL
           | |- ?G => idtac "LEFT:" G
           end. }
    intros [msF2 mo2] PO. unfold free_null_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                    VIS2 & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & HEAP2 & AC2 & AL2).
    apply (ah_done H HH).
    unfold cfree_null_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s'.
    split; [exact VIS2|]. split; [exact KREL2|]. split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR2|]. split; [exact AUX2|].
    split.
    { eapply xpres_trans.
      - eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|].
        constructor; [left; cbn; lia| constructor].
      - apply xpres_of_apres. exact HPRES. }
    split; [exact HEAP2|].
    split.
    { destruct IM1 as (I1 & I2 & I3). unfold IMPL_mem.
      repeat split; (eapply (apres_rw_cells H); [exact HPRES| eassumption|]); right; left; unfold A_malloc_impl, A_realloc_impl, A_free_impl, aimg_client; cbn; lia. }
    split.
    { eapply (apres_rw_cells H); [exact HPRES| exact GM1|]. right; left. unfold A_got_CRYPTO_malloc, aimg_client. cbn. lia. }
    exact AL2.
  Qed.
End W.
