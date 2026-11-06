(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_LibState ECH_C0_stmt ECH_C1_stmt ECH_C2_stmt ECH_LibFrame ECH_C4_stmt ECH_C4_rep ECH_C4_frame ECH_C4_frame2 ECH_C11_stmt ECH_C11_find ECH_C11_fail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SC_RA_KEM : Z := 0x2b41f0.  Definition SC_RA_KDF : Z := 0x2b4200.  Definition SC_RA_AEAD : Z := 0x2b4210.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br_not := step; try (let K0 := fresh "K0" in if_cases K0; zify_cond K0; [kill K0|]; clear K0).

  (* [comment removed for export] *)
  Definition sc_call_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (pcv rav a0v lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 s0i s1i a1 a2 a3 a4 a5 a6 a7 s2i s3i s4i s5i s6i t3 t4 t5 t6 m',
      ms' = MS (mkR (Z_to_bv 64 rav) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0i s1i (Z_to_bv 64 a0v) a1 a2 a3 a4 a5 a6 a7
                    s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pcv) fc None m' (seg_rom usegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -64)
      /\ rw_cells usegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ HPKE_tabs m'.

  Lemma sb_segK : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (kem kdf aead hi lo : Z),
      0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 -> HPKE_tabs m ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_OK_STACK -> mem_inv usegs m ->
      evt usegs (sc_call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P_ossl_HPKE_KEM_INFO_find_id SC_RA_KEM kem lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (suite_word kem kdf aead hi)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros KR DR AR HR TB ST CEIL LO MI.
    unfold sc_call_post, P_OSSL_HPKE_suite_check, SUITECHECK_OK_STACK, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id, suite_word, SC_RA_KEM, P_ossl_HPKE_KEM_INFO_find_id in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    do 4 st1. step. step. rewrite suite_mask48 by lia.
    step. step. step. st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp).
    carve_frame 64%nat ST. do 10 st1. step. step. step. step. step. step.
    rewrite suite_kem by lia. step.
    finish.
    eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia.
  Qed.

  Lemma sb_segD : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (kem kdf aead hi lo : Z) (ik : nat),
      0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 -> HPKE_tabs m ->
      find_id HPKE_KEM_IDS kem = Some ik ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_OK_STACK -> mem_inv usegs m ->
      evt usegs (sc_call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P_ossl_HPKE_KDF_INFO_find_id SC_RA_KDF kdf lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (suite_word kem kdf aead hi)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom usegs)).
  Proof.
    intros until ik. intros KR DR AR HR TB FK ST CEIL LO MI.
    unfold sc_call_post, P_OSSL_HPKE_suite_check, SUITECHECK_OK_STACK, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id, suite_word, SC_RA_KDF, P_ossl_HPKE_KDF_INFO_find_id in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (find_id_lt _ _ _ FK) as BK. cbn [length HPKE_KEM_IDS] in BK.
    carve_frame 16%nat ST.
    do 4 st1. step. step. rewrite suite_mask48 by lia.
    step. step. step. st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp).
    carve_frame 64%nat ST. do 10 st1. step. step. step. step. step. step.
    rewrite suite_kem by lia. step.
    assert (TB1 : HPKE_tabs m1).
    { eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia. }
    eapply evt_cut.
    { eapply (hfind_found_kem) with (lo := lo) (i := ik) (id := kem); try reflexivity; try eassumption; try lia.
      all: cbn [f_frame KEM_finder]; unfold FR_ossl_HPKE_KEM_INFO_find_id; rewrite ?unsigned_lit by lia; first [eassumption | lia | reflexivity]. }
    intros ms' PO. unfold hfind_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST' & TB').
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI TB1 ST. rename MI' into MI. rename ST' into ST.
    cbn [f_tab f_stride KEM_finder]. unfold A_hpke_kem_tab, HPKE_KEM_ROW.
    br_not. step. step. rewrite suite_kdf by lia. step.
    finish.
  Qed.

  Lemma sb_segA : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (kem kdf aead hi lo : Z) (ik idf : nat),
      0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 -> HPKE_tabs m ->
      find_id HPKE_KEM_IDS kem = Some ik -> find_id HPKE_KDF_IDS kdf = Some idf ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_OK_STACK -> mem_inv usegs m ->
      evt usegs (sc_call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P_ossl_HPKE_AEAD_INFO_find_id SC_RA_AEAD aead lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (suite_word kem kdf aead hi)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom usegs)).
  Proof.
    intros until idf. intros KR DR AR HR TB FK FD ST CEIL LO MI.
    unfold sc_call_post, P_OSSL_HPKE_suite_check, SUITECHECK_OK_STACK, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id, suite_word, SC_RA_AEAD, P_ossl_HPKE_AEAD_INFO_find_id in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (find_id_lt _ _ _ FK) as BK. pose proof (find_id_lt _ _ _ FD) as BD. cbn [length HPKE_KEM_IDS HPKE_KDF_IDS] in BK, BD.
    carve_frame 16%nat ST.
    do 4 st1. step. step. rewrite suite_mask48 by lia.
    step. step. step. st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp).
    carve_frame 64%nat ST. do 10 st1. step. step. step. step. step. step.
    rewrite suite_kem by lia. step.
    assert (TB1 : HPKE_tabs m1).
    { eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia. }
    eapply evt_cut.
    { eapply (hfind_found_kem) with (lo := lo) (i := ik) (id := kem); try reflexivity; try eassumption; try lia.
      all: cbn [f_frame KEM_finder]; unfold FR_ossl_HPKE_KEM_INFO_find_id; rewrite ?unsigned_lit by lia; first [eassumption | lia | reflexivity]. }
    intros ms' PO. unfold hfind_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & ST' & TB').
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI TB1 ST. rename MI' into MI. rename ST' into ST.
    cbn [f_tab f_stride KEM_finder]. unfold A_hpke_kem_tab, HPKE_KEM_ROW.
    br_not. step. step. rewrite suite_kdf by lia. step.
    eapply evt_cut.
    { eapply (hfind_found_kdf) with (lo := lo) (i := idf) (id := kdf); try reflexivity; try eassumption; try lia.
      all: cbn [f_frame KDF_finder]; unfold FR_ossl_HPKE_KDF_INFO_find_id; rewrite ?unsigned_lit by lia; first [eassumption | lia | reflexivity]. }
    intros ms' PO. unfold hfind_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'' & -> & MU' & WM' & MI' & ST' & TB'').
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI TB' ST. rename MI' into MI. rename ST' into ST.
    cbn [f_tab f_stride KDF_finder]. unfold A_hpke_kdf_tab, HPKE_KDF_ROW.
    br_not. step. step. rewrite suite_aead by lia. step.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma sb_segE : forall (RA : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s0i s1i s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : mem) (lo : Z),
      RA = SC_RA_KEM \/ RA = SC_RA_KDF \/ RA = SC_RA_AEAD ->
      rw_cells usegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk usegs m' lo (bv_unsigned sp + -64) -> mem_inv usegs m' -> hceil <= lo -> lo <= bv_unsigned sp - 64 ->
      evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom usegs) /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 s0i s1i (Z_to_bv 64 0) b1 b2 b3 b4 b5 b6 b7
                 s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc (Z_to_bv 64 RA)) fc None m' (seg_rom usegs)).
  Proof.
    intros until lo. intros HRA FR ST MI CEIL LO. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct HRA as [-> | [-> | ->]]; unfold SC_RA_KEM, SC_RA_KDF, SC_RA_AEAD.
    all: match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    all: step; try if_true; step; step; do 8 st1; step; step; release_frame FR ST (bv_unsigned sp); finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.

  (* [comment removed for export] *)
  Lemma suitebad_case : forall (f : finder) (RA idv : Z),
    hfind_fail_stmt H f -> 0 <= f_frame f <= 32 -> RA = SC_RA_KEM \/ RA = SC_RA_KDF \/ RA = SC_RA_AEAD ->
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (errv : word),
      0 <= idv < 2^16 -> find_id (f_ids f) idv = None ->
      evt usegs (sc_call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f_entry f) RA idv lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom usegs)) ->
      hs_RHEAP H s (blocks_ERRST E ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (blocks_ERRST E ++ LB) + raise_bytes ph <= hs_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + raise_cnt ph <= hs_LIVE_CNT_MAX H ->
      lb_big (blocks_ERRST E ++ LB) + errph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_STACK ph ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> relro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph lo -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (hfind_fail_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB ph E x (f_reason f) (f_line f idv) lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom usegs)) mo).
  Proof using HX.
    intros f RA idv FAIL FRR HRA. intros until errv.
    intros IDR FI PRE HP KREL BY CN BG AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL EP EX EB CP RAE.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (RS0 : 0 <= RAISE_STACK ph).
    { unfold RAISE_STACK, ERRDEBUG_STACK, FR_ERR_set_debug, CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK. lia. }
    unfold SUITECHECK_STACK, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id in LO.
    set (SB := blocks_ERRST E) in *.
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (RBL : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (HH_RHEAP_block_range H HH); [exact HP| apply SUBx; exact Hb]. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| exact PRE|].
    intros ms1 (t0' & t1' & t2' & s0i & s1i & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2i & s3i & s4i & s5i & s6i & t3' & t4' & t5' & t6' & m1 &
                -> & MU1 & WM1 & MI1 & ST1 & FR1 & TB1).
    set (spi := Z_to_bv 64 (bv_unsigned sp + -64)) in *.
    assert (SPI : bv_unsigned spi = bv_unsigned sp + -64) by (unfold spi; rewrite unsigned_lit by lia; reflexivity).
    assert (FW1 : Forall stack_or_errno [(lo, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (CW1 : C4W LB m1 ph x).
    { eapply C4W_stack; [| exact MU1| exact WM1| exact FW1| exact RBL]. unfold C4W. tauto. }
    destruct CW1 as (MF1 & IM1 & GM1 & RL1 & EP1 & CP1).
    assert (HP1 : hs_RHEAP H s (SB ++ LB) m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    assert (ERR1 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
    { subst tp. rewrite errno_RATP in *. eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. unfold RERRNO. cbn. lia. }
    assert (EX1 : ERRX m1 ph E).
    { destruct ph as [|c0]; [exact EX|]. cbn [ERRX] in *. eapply ERRST_munch; [exact EX| exact MU1| exact WM1|].
      cbn [errph_below] in EB. unfold chain_below in EB. unfold ERRST_SIZE in *. cbn. lia. }
    (* [comment removed for export] *)
    eapply (sr_seq H HH).
    { unfold hfind_fail_stmt in FAIL.
      eapply FAIL with (id := idv) (lo := lo) (B := B) (LB := LB) (s := s) (ph := ph) (E := E) (x := x) (errv := errv);
        try reflexivity; try eassumption; try (rewrite SPI); try eassumption; try (clear - SPA SPI; lia); try (clear - LO FRR; lia); try (clear - SPB; lia).
      destruct HRA as [-> | [-> | ->]]; reflexivity. }
    intros [ms2 mo2] PO. unfold hfind_fail_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & errv' & s' & LBN & c & p1 & p2 & A1 & n1 & A2 & n2 &
                    -> & MP' & (KREL' & MI' & ST' & AUX' & HP' & MF' & IM' & GM' & RL') & ERR' & DL & RSZ & EP' & CP' & EST' & TB' & XP').
    rewrite SPI in ST', XP'.
    assert (FX : Forall (fun iv : Z * Z => bv_unsigned sp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) <= fst iv \/ snd iv <= bv_unsigned sp + -64)
                        (ERR_X ++ memflag_foot ++ errph_foot ph)).
    { apply Forall_app. split; [| apply Forall_app; split].
      - unfold ERR_X, A_err_string_once, A_defctx_inited, A_tevent_once, A_load_strings_once, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
      - destruct ph as [|c0]; [constructor|]. cbn [errph_foot errph_below] in *. unfold chain_below in EB. unfold ERRST_SIZE in *. constructor; [cbn; lia| constructor]. }
    pose proof (xpres_rw_cells' _ _ _ _ _ _ _ XP' FR1 ltac:(left; lia) FX) as FR'.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL'| eapply sb_segE with (lo := lo) (s0 := s0) (s1 := s1) (ra := ra); try eassumption; lia|].
    intros ms3 (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & -> & ST3).
    apply (sr_done H HH). unfold hfind_fail_post. cbn [cfg_ms cfg_model].
    exists w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m', errv', s', LBN, c, p1, p2, A1, n1, A2, n2.
    split; [reflexivity|]. split; [exact MP'|]. split; [unfold c4_frame; cbn [cfg_model]; tauto|].
    split; [exact ERR'|]. split; [exact DL|]. split; [exact RSZ|]. split; [exact EP'|]. split; [exact CP'|]. split; [exact EST'|].
    split; [exact TB'|].
    eapply xpres_trans.
    - eapply xpres_of_munch; [exact MU1| exact WM1| |].
      + constructor; [left; cbn; lia| constructor].
      + intros b Hb. pose proof (RBL b Hb) as RB. unfold rblock_range in RB. lia.
    - eapply xpres_weaken; [exact XP'| lia| auto| auto].
  Qed.

  Lemma suitebad_spec : suitebad_stmt H.
  Proof using HX EGS.
    unfold suitebad_stmt. intros until errv.
    intros A0 KR DR AR HR SF TB HP KREL BY CN BG AUX SPB SPA ST CEIL LO ERR MI TP MF IM GM RL EP EX EB CP RAE. subst a0.
    assert (LOK : lo <= bv_unsigned sp - SUITECHECK_OK_STACK).
    { assert (RS0 : 0 <= RAISE_STACK ph).
      { unfold RAISE_STACK, ERRDEBUG_STACK, FR_ERR_set_debug, CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK. lia. }
      unfold SUITECHECK_STACK, SUITECHECK_OK_STACK in *. lia. }
    unfold suite_fail in SF.
    destruct (find_id HPKE_KEM_IDS kem) as [ik|] eqn:FK.
    2: { injection SF as <- <-.
         eapply (suitebad_case KEM_finder SC_RA_KEM kem (hfind_fail_kem H HX EGS)) with (lo := lo) (B := B) (errv := errv); try eassumption;
           try (cbn [f_frame KEM_finder]; unfold FR_ossl_HPKE_KEM_INFO_find_id; lia); try (left; reflexivity).
         eapply sb_segK; eassumption. }
    destruct (find_id HPKE_KDF_IDS kdf) as [idf|] eqn:FD.
    2: { injection SF as <- <-.
         eapply (suitebad_case KDF_finder SC_RA_KDF kdf (hfind_fail_kdf H HX EGS)) with (lo := lo) (B := B) (errv := errv); try eassumption;
           try (cbn [f_frame KDF_finder]; unfold FR_ossl_HPKE_KDF_INFO_find_id; lia); try (right; left; reflexivity).
         eapply sb_segD; eassumption. }
    destruct (find_id HPKE_AEAD_IDS aead) as [ia|] eqn:FA; [discriminate SF|]. injection SF as <- <-.
    eapply (suitebad_case AEAD_finder SC_RA_AEAD aead (hfind_fail_aead H HX EGS)) with (lo := lo) (B := B) (errv := errv); try eassumption;
      try (cbn [f_frame AEAD_finder]; unfold FR_ossl_HPKE_AEAD_INFO_find_id; lia); try (right; right; reflexivity).
    eapply sb_segA; eassumption.
  Qed.
End W.
