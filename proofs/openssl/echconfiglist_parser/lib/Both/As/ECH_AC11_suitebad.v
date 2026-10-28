(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C2 ECH_AStmt_C4 ECH_AStmt_C11 ECH_AKit ECH_AsKit ECH_ARostr ECH_AC11_find ECH_AC11_fail.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SC_RA_KEM : Z := 0x5554a4.  Definition SC_RA_KDF : Z := 0x5554b8.  Definition SC_RA_AEAD : Z := 0x5554cc.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit by lia; lia.
  Local Ltac br_not := step; try (let K0 := fresh "K0" in if_cases K0; zify_cond K0; [kill K0|]; clear K0).
  Local Ltac finish_jk := apply evt_done; hnf; repeat (lazymatch goal with |- ex _ => eexists end);
    lazymatch goal with
    | |- _ = _ /\ _ => split; [reflexivity|]; repeat match goal with |- _ /\ _ => split end; try assumption;
                        try (lazymatch goal with |- rw_cells _ _ _ _ => eassumption end)
    end.

  (* [comment removed for export] *)
  Definition sc_call_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (pcv rav a0v lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 s1i a1 a2 a3 a4 a5 a6 a7 s2i s3i s4i s5i s6i s7i t3 t4 t5 t6 m' jk,
      ms' = MS (mkR (Z_to_bv 64 rav) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp s1i (Z_to_bv 64 a0v) a1 a2 a3 a4 a5 a6 a7
                    s2i s3i s4i s5i s6i s7i s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pcv) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp + -80)
      /\ rw_cells asegs m' (bv_unsigned sp + -80) [CB 8 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ HPKE_tabs m'.

  Lemma sb_segK : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (kem kdf aead hi lo : Z),
      0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 -> HPKE_tabs m -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_OK_STACK -> mem_inv asegs m ->
      evt asegs (sc_call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P_ossl_HPKE_KEM_INFO_find_id SC_RA_KEM kem lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (suite_word kem kdf aead hi)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros KR DR AR HR TB AC ST CEIL LO MI.
    unfold sc_call_post, P_OSSL_HPKE_suite_check, SUITECHECK_OK_STACK, FR_OSSL_HPKE_suite_check, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id, suite_word, SC_RA_KEM, P_ossl_HPKE_KEM_INFO_find_id in *. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    carve_frame 16%nat ST.
    do 4 step. step. step. rewrite suite_mask48 by lia.
    step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    carve_frame 80%nat ST. do 11 step. step. step. step. step. step. step. step. step. step.
    rewrite suite_kem by lia. step. step.
    finish_jk.
    - eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL].
    - eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia.
  Qed.

  Lemma sb_segD : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (kem kdf aead hi lo : Z) (ik : nat),
      0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 -> HPKE_tabs m -> ACONST m ->
      find_id HPKE_KEM_IDS kem = Some ik ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_OK_STACK -> mem_inv asegs m ->
      evt asegs (sc_call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P_ossl_HPKE_KDF_INFO_find_id SC_RA_KDF kdf lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (suite_word kem kdf aead hi)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom asegs)).
  Proof.
    intros until ik. intros KR DR AR HR TB AC FK ST CEIL LO MI.
    unfold sc_call_post, P_OSSL_HPKE_suite_check, SUITECHECK_OK_STACK, FR_OSSL_HPKE_suite_check, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id, suite_word, SC_RA_KDF, P_ossl_HPKE_KDF_INFO_find_id in *. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (find_id_lt _ _ _ FK) as BK. cbn [length HPKE_KEM_IDS] in BK.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    carve_frame 16%nat ST.
    do 4 step. step. step. rewrite suite_mask48 by lia.
    step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    carve_frame 80%nat ST. do 11 step. step. step. step. step. step. step. step. step. step.
    rewrite suite_kem by lia. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (TB1 : HPKE_tabs m1).
    { eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia. }
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]).
    eapply evt_cut.
    { eapply (ahfind_found_kem) with (lo := lo) (i := ik) (id := kem); try reflexivity; try eassumption; try lia.
      all: cbn [f_frame KEM_finder]; unfold FR_ossl_HPKE_KEM_INFO_find_id; rewrite ?unsigned_lit by lia; first [eassumption | lia | reflexivity]. }
    intros ms' PO. unfold hfind_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & AC' & ST' & TB').
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI TB1 ST AC1. rename MI' into MI. rename ST' into ST.
    cbn [f_tab f_stride KEM_finder]. unfold A_hpke_kem_tab, HPKE_KEM_ROW.
    br_not. step. step. rewrite suite_kdf by lia. step. step.
    finish_jk; assumption.
  Qed.

  Lemma sb_segA : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (kem kdf aead hi lo : Z) (ik idf : nat),
      0 <= kem < 2^16 -> 0 <= kdf < 2^16 -> 0 <= aead < 2^16 -> 0 <= hi < 2^16 -> HPKE_tabs m -> ACONST m ->
      find_id HPKE_KEM_IDS kem = Some ik -> find_id HPKE_KDF_IDS kdf = Some idf ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_OK_STACK -> mem_inv asegs m ->
      evt asegs (sc_call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P_ossl_HPKE_AEAD_INFO_find_id SC_RA_AEAD aead lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (suite_word kem kdf aead hi)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom asegs)).
  Proof.
    intros until idf. intros KR DR AR HR TB AC FK FD ST CEIL LO MI.
    unfold sc_call_post, P_OSSL_HPKE_suite_check, SUITECHECK_OK_STACK, FR_OSSL_HPKE_suite_check, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id, suite_word, SC_RA_AEAD, P_ossl_HPKE_AEAD_INFO_find_id in *. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (find_id_lt _ _ _ FK) as BK. pose proof (find_id_lt _ _ _ FD) as BD. cbn [length HPKE_KEM_IDS HPKE_KDF_IDS] in BK, BD.
    pose proof (ACONST_shbase _ AC) as [GSB SHB]; unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB; rewrite ASHADOW_BASE_val in SHB.
    carve_frame 16%nat ST.
    do 4 step. step. step. rewrite suite_mask48 by lia.
    step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    carve_frame 80%nat ST. do 11 step. step. step. step. step. step. step. step. step. step.
    rewrite suite_kem by lia. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (TB1 : HPKE_tabs m1).
    { eapply HPKE_tabs_transport; [exact MU | exact WM | | exact TB]. unfold HPKE_TAB_LO, HPKE_TAB_HI, A_hpke_kem_tab, A_hpke_aead_tab; cbn; lia. }
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]).
    eapply evt_cut.
    { eapply (ahfind_found_kem) with (lo := lo) (i := ik) (id := kem); try reflexivity; try eassumption; try lia.
      all: cbn [f_frame KEM_finder]; unfold FR_ossl_HPKE_KEM_INFO_find_id; rewrite ?unsigned_lit by lia; first [eassumption | lia | reflexivity]. }
    intros ms' PO. unfold hfind_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU' & WM' & MI' & AC' & ST' & TB').
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI TB1 ST AC1. rename MI' into MI. rename ST' into ST. rename AC' into AC1.
    cbn [f_tab f_stride KEM_finder]. unfold A_hpke_kem_tab, HPKE_KEM_ROW.
    br_not. step. step. rewrite suite_kdf by lia. step. step.
    eapply evt_cut.
    { eapply (ahfind_found_kdf) with (lo := lo) (i := idf) (id := kdf); try reflexivity; try eassumption; try lia.
      all: cbn [f_frame KDF_finder]; unfold FR_ossl_HPKE_KDF_INFO_find_id; rewrite ?unsigned_lit by lia; first [eassumption | lia | reflexivity]. }
    intros ms' PO. unfold hfind_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'' & -> & MU' & WM' & MI' & AC' & ST' & TB'').
    match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite unsigned_lit in MU', ST' by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI TB' ST AC1. rename MI' into MI. rename ST' into ST.
    cbn [f_tab f_stride KDF_finder]. unfold A_hpke_kdf_tab, HPKE_KDF_ROW.
    br_not. step. step. rewrite suite_aead by lia. step. step.
    finish_jk; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma sb_segE : forall (RA : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s1i s2i s3i s4i s5i s6i s7i s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : mem) (lo : Z) (jk : list byte),
      RA = SC_RA_KEM \/ RA = SC_RA_KDF \/ RA = SC_RA_AEAD ->
      rw_cells asegs m' (bv_unsigned sp + -80) [CB 8 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk asegs m' lo (bv_unsigned sp + -80) -> mem_inv asegs m' -> aceil <= lo -> lo <= bv_unsigned sp - 80 ->
      evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom asegs) /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp u0 u1 u2 sp s1i (Z_to_bv 64 0) b1 b2 b3 b4 b5 b6 b7
                 s2i s3i s4i s5i s6i s7i s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc (Z_to_bv 64 RA)) fc None m' (seg_rom asegs)).
  Proof.
    intros until jk. intros HRA FR ST MI CEIL LO. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct HRA as [-> | [-> | ->]]; unfold SC_RA_KEM, SC_RA_KDF, SC_RA_AEAD.
    all: match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    all: step; try if_true; try if_lit; step; step; do 9 step; step; step; release_frame FR ST (bv_unsigned sp); finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis RAISE : araise_stmt H.

  (* [comment removed for export] *)
  Lemma asuitebad_case : forall (f : finder) (RA idv : Z),
    hfind_fail_stmt H f -> 0 <= f_frame f <= 32 -> RA = SC_RA_KEM \/ RA = SC_RA_KDF \/ RA = SC_RA_AEAD ->
    (forall ph x0, In x0 (pf_shift RA (PF_hfind f ph)) -> In x0 (PF_suitebad ph)) ->
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (ph : errphase) (E : errst) (x : ctxinfo) (lo B : Z) (errv : word) (CH : list (Z * Z)),
      0 <= idv < 2^16 -> find_id (f_ids f) idv = None ->
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom asegs) ->
      evt asegs (sc_call_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f_entry f) RA idv lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_HPKE_suite_check) fc None m (seg_rom asegs)) ->
      as_RHEAP H s (blocks_ERRST E ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (blocks_ERRST E ++ LB) + raise_bytes ph <= as_LIVE_MAX H ->
      Z.of_nat (length (blocks_ERRST E ++ LB)) + raise_cnt ph <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - SUITECHECK_STACK ph -> errph_sh0 ph m lo sp ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m ->
      ERRPH LB m ph -> ERRX m ph E -> errph_below ph aceil -> errph_shad m ph -> CTXPH LB m (CtxReady x) -> bv_unsigned ra mod 2 = 0 ->
      as_RFS H LF m -> (length LF + ERRPH_LF ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_suitebad ph) (bv_unsigned ra) CH -> errph_closed_ok H ph -> RAISE_COST H ph <= as_AL H s ->
      as_SR H (hfind_fail_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ph E x (f_reason f) (f_line f idv) lo B m mo)
        (mkCfg msF mo).
  Proof using HH.
    intros f RA idv FAIL FRR HRA PFI. intros until CH.
    intros IDR FI VIS PRE HP KREL BY CN AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL EP EX EB ESH CP RAE RFS LFB CHN CHS PF ECL HAL.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (RS0 : 0 <= RAISE_STACK ph).
    { unfold RAISE_STACK, ERRDEBUG_STACK, FR_ERR_set_debug, CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK. lia. }
    unfold SUITECHECK_STACK, FR_OSSL_HPKE_suite_check, FR_hpke_suite_check, FR_ossl_HPKE_KEM_INFO_find_id in LO.
    set (SB := blocks_ERRST E) in *.
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    assert (RAR2 : 0 <= RA < 2^64 /\ RA mod 2 = 0) by (destruct HRA as [-> |[-> | ->]]; unfold SC_RA_KEM, SC_RA_KDF, SC_RA_AEAD; split; try lia; reflexivity).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| exact PRE|].
    intros msF1 mo1 KREL1 MP1 (t0' & t1' & t2' & s1i & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2i & s3i & s4i & s5i & s6i & s7i & t3' & t4' & t5' & t6' & m1 & jk &
                VIS1 & MU1 & WM1 & MI1 & AC1 & ST1 & FR1 & TB1).
    set (spi := Z_to_bv 64 (bv_unsigned sp + -80)) in *.
    assert (SPI : bv_unsigned spi = bv_unsigned sp + -80) by (unfold spi; rewrite unsigned_lit by lia; reflexivity).
    assert (AG1 : magree (lib_addr LB) m m1).
    { eapply magree_of_munch; [exact MU1| exact WM1|]. intros a Ha. eapply (lib_addr_off_stack H HH); [exact HP| exact SUBx| exact CEIL| exact Ha]. }
    assert (MF1 : MEMFLAG m1 1) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (RL1 : arelro_lib m1) by (eapply arelro_across; [exact RL| exact MU1| constructor; [cbn; lia| constructor]]).
    assert (EP1 : ERRPH LB m1 ph) by (eapply ERRPH_frame; [exact EP| exact AG1]).
    assert (CP1 : CTXPH LB m1 (CtxReady x)) by (eapply CTXPH_frame; [exact CP| exact AG1]).
    assert (CW : Forall (aclient_write_ok H (SB ++ LB)) [(lo, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (HP1 : as_RHEAP H s (SB ++ LB) m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (AGS : magree (lib_addr SB) m m1).
    { eapply magree_of_munch; [exact MU1| exact WM1|]. intros a Ha. eapply (lib_addr_off_stack H HH); [exact HP| intros b Hb; apply in_or_app; left; exact Hb| exact CEIL| exact Ha]. }
    assert (EX1 : ERRX m1 ph E).
    { destruct ph as [|c0]; [exact EX|]. cbn [ERRX] in *. destruct EX as (EXa & EXb & EXc & EXd). split; [| split; [exact EXb| split]].
      - eapply ERRST_agree; [| exact EXa| intros x0 Hx0; exact Hx0].
        eapply magree_of_munch; [exact MU1| exact WM1|]. intros a Ha. cbn [errph_below] in EB. unfold chain_below, in_range, ERRST_SIZE in *. cbn. lia.
      - eapply lib_shad_frame; [exact EXc| exact AGS].
      - (* [comment removed for export] *)
        unfold estrs_cells in *. apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) EXd _ Hb) as [bs BC]. exists bs.
        eapply rw_cells_agree; [exact AGS| exact BC|]. intros a Ha. right; left. exists b. split; [exact Hb|].
        unfold in_range in Ha. pose proof (rw_cells_bound _ _ _ _ BC) as BB. revert Ha BB. cbn [cells_size csize]. rewrite Nat.add_0_r.
        pose proof (ah_blocks H HH _ _ _ _ HP (in_or_app _ _ _ (or_introl Hb))) as (_ & _ & B3 & _). rewrite Z2Nat.id by lia. intros Ha BB. lia. }
    assert (ESH1 : errph_shad m1 ph).
    { destruct ph as [|c0]; [exact I|]. cbn [errph_shad] in ESH |- *. cbn [ERRPH] in EP. destruct EP as [_ ECx].
      eapply lib_shad_frame; [exact ESH|]. eapply magree_mono; [exact AG1|]. intros a Ha. eapply lib_addr_mono; [| exact Ha].
      intros b Hb. eapply chain_blocks_in; [exact ECx| exact Hb]. }
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4).
    assert (RFS1 : as_RFS H LF m1).
    { eapply (ah_RFS_frame H HH); [exact RFS| exact MU1| exact WM1|]. constructor; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia| constructor]. }
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof FR1 as FR2.
      change ([CB 8 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -80 + 64) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned spi + 16 <= fp').
    { rewrite SPI. intros fp' ra' [Ex|Hin]; [injection Ex as <- <-; lia| specialize (CHS _ _ Hin); lia]. }
    assert (PF1 : pf_ok (as_TR H) (PF_hfind f ph) RA ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply pf_ok_call; [exact PF| exact (PFI ph)]. }
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { unfold hfind_fail_stmt in FAIL.
      eapply FAIL with (id := idv) (lo := lo) (B := B) (LB := LB) (s := s) (ph := ph) (E := E) (x := x) (errv := errv) (LF := LF)
                        (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| ..]; try reflexivity; try eassumption; try (rewrite SPI); try eassumption; try (clear - SPA SPI; lia); try (clear - LO FRR RS0; lia); try (clear - SPB; lia).
      all: lazymatch goal with
           | |- rw_cells _ _ (errno_addr _) _ => rewrite unsigned_lit by (unfold ATP; lia); exact ERR1
           | |- _ mod 2 = 0 => rewrite unsigned_lit by lia; exact (proj2 RAR2)
           | |- pf_ok _ _ _ _ => rewrite unsigned_lit by lia; exact PF1
           | |- errph_shad _ _ => exact ESH1
           | |- errph_closed_ok _ _ => exact ECL
           | |- errph_sh0 _ _ _ _ => eapply errph_sh0_sub; [eapply errph_sh0_munch; [exact SH0| exact MU1| exact WM1| apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO; lia| apply Forall_nil]]
                                      | rewrite ?SPI, ?unsigned_lit by lia; clear - SPR LO RS0 LO0 ACEILB CEIL; lia
                                      | rewrite ?SPI, ?unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia]
           | |- ?G => first [lia| idtac "LEFT:" G]
           end. }
    intros [msF2 mo2] PO. unfold hfind_fail_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & errv' & s' & LBN & c & p1 & p2 & A1 & n1 & A2 & n2 & XS &
                    VIS2 & MP' & (KREL' & MI' & AC' & ST' & AUX' & HP' & MF' & IM' & GM' & RL') & ERR' & DL & RSZ & EP' & CP' & EST' & ESH' & TB' & FXS & XP' & RFS' & AL').
    rewrite SPI in ST', XP'.
    assert (LOS : lo <= bv_unsigned sp + -80) by lia.
    pose proof (raise_foot_frame ph (bv_unsigned sp + -80) (Z.of_nat (cells_size [CB 8 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) lo CEIL LOS EB) as FX0.
    pose proof (scratch_foot_frame H HH LF m1 XS (bv_unsigned sp + -80) (Z.of_nat (cells_size [CB 8 jk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) lo RFS1 FXS CEIL LOS) as FX1.
    pose proof (proj2 (Forall_app _ _ _) (conj FX1 FX0)) as FX.
    pose proof (xpres_rw_cells' H _ _ _ _ _ _ _ XP' FR1 ltac:(left; lia) FX) as FR'.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL'| exact VIS2| eapply sb_segE with (lo := lo) (s1 := s1) (ra := ra); try eassumption; lia|].
    intros msF3 mo3 KREL3 MP3 (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & VIS3 & ST3).
    eapply (ah_done H HH). unfold hfind_fail_post. cbn [cfg_ms cfg_model].
    exists w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m', errv', s', LBN, c, p1, p2, A1, n1, A2, n2, XS.
    split; [exact VIS3|].
    split; [eapply (ah_mpres_trans H HH); [| exact MP3]; eapply (ah_mpres_trans H HH); [exact MP1| exact MP']|].
    split; [unfold c4_frame; repeat match goal with |- _ /\ _ => split end; assumption|].
    split; [exact ERR'|]. split; [exact DL|]. split; [exact RSZ|]. split; [exact EP'|]. split; [exact CP'|]. split; [exact EST'|]. split; [exact ESH'|].
    split; [exact TB'|]. split; [exact FXS|].
    split.
    - eapply xpres_trans.
      + eapply (xpres_weaken H (SB ++ LB) LB); [| apply Z.le_refl| exact SUBx| intros ax K; exact K].
        eapply (xpres_of_munch H s (SB ++ LB) _ _ _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor].
      + eapply (xpres_weaken H LB LB); [exact XP'| lia| auto| auto].
    - split; [exact RFS'| exact AL'].
  Qed.

  Lemma asuitebad_spec : suitebad_stmt H.
  Proof using HH RAISE.
    unfold suitebad_stmt. intros until CH.
    intros VIS A0 KR DR AR HR SF TB HP KREL BY CN AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL EP EX EB ESH CP RAE RFS LFB CHN CHS PF ECL HAL. subst a0.
    assert (LOK : lo <= bv_unsigned sp - SUITECHECK_OK_STACK).
    { assert (RS0 : 0 <= RAISE_STACK ph).
      { unfold RAISE_STACK, ERRDEBUG_STACK, FR_ERR_set_debug, CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK. lia. }
      unfold SUITECHECK_STACK, SUITECHECK_OK_STACK in *. lia. }
    unfold suite_fail in SF.
    destruct (find_id HPKE_KEM_IDS kem) as [ik|] eqn:FK.
    2: { injection SF as <- <-.
         eapply (asuitebad_case KEM_finder SC_RA_KEM kem (ahfind_fail_kem H HH RAISE)) with (lo := lo) (B := B) (errv := errv) (CH := CH); try eassumption;
           try (cbn [f_frame KEM_finder]; unfold FR_ossl_HPKE_KEM_INFO_find_id; lia); try (left; reflexivity).
         - intros ph0 x0 Hx. unfold PF_suitebad. apply in_or_app. left. exact Hx.
         - eapply sb_segK; eassumption. }
    destruct (find_id HPKE_KDF_IDS kdf) as [idf|] eqn:FD.
    2: { injection SF as <- <-.
         eapply (asuitebad_case KDF_finder SC_RA_KDF kdf (ahfind_fail_kdf H HH RAISE)) with (lo := lo) (B := B) (errv := errv) (CH := CH); try eassumption;
           try (cbn [f_frame KDF_finder]; unfold FR_ossl_HPKE_KDF_INFO_find_id; lia); try (right; left; reflexivity).
         - intros ph0 x0 Hx. unfold PF_suitebad. apply in_or_app. right. apply in_or_app. left. exact Hx.
         - eapply sb_segD; eassumption. }
    destruct (find_id HPKE_AEAD_IDS aead) as [ia|] eqn:FA; [discriminate SF|]. injection SF as <- <-.
    eapply (asuitebad_case AEAD_finder SC_RA_AEAD aead (ahfind_fail_aead H HH RAISE)) with (lo := lo) (B := B) (errv := errv) (CH := CH); try eassumption;
      try (cbn [f_frame AEAD_finder]; unfold FR_ossl_HPKE_AEAD_INFO_find_id; lia); try (right; right; reflexivity).
    - intros ph0 x0 Hx. unfold PF_suitebad. apply in_or_app. right. apply in_or_app. right. exact Hx.
    - eapply sb_segA; eassumption.
  Qed.
End W.
