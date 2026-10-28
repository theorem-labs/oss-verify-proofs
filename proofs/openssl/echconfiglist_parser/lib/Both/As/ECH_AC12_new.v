(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13 ECH_AStmt_C12 ECH_AKit ECH_AsKit ECH_AC1_malloc ECH_AC1_zalloc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition AVPM_FILE : Z := 0xc3200.        (* [comment removed for export] *)
  Definition AVN_RA : Z := R_X509_VERIFY_PARAM_new_CRYPTO_zalloc.   (* [comment removed for export] *)
  Definition SHB : Z := 0x7fff8000.
  Definition avn_frame (j : list byte) (s1 s0 ra : word) : list cell := [CB 8 j; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition vpm_zero_cells : list cell :=
    [CB 36 (zeros 36); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  Definition vpm_new_cells : list cell :=
    [CB 36 (zeros 36); C4 (wz 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  Lemma vpm_zero_recut : forall m A, rw_cells asegs m A [CB (Z.to_nat 136) (zeros (Z.to_nat 136))] -> rw_cells asegs m A vpm_zero_cells.
  Proof. intros m A HB. eapply arw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.
  Lemma bytes_eq_map : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
  Proof.
    induction l1 as [|b l1 IH]; intros [|b' l2] E; cbn in E; try discriminate; [reflexivity|].
    injection E as E1 E2. f_equal; [apply bv_eq; exact E1| apply IH; exact E2].
  Qed.
  (* [comment removed for export] *)
  Lemma vpm_new_recut : forall m A id, rw_cells asegs m A vpm_new_cells -> rw_cells asegs m A (vpm_cells (vpm_empty id)).
  Proof. intros m A id HB. eapply arw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| apply bytes_eq_map; vm_compute; reflexivity]. Qed.

  (* [comment removed for export] *)
  Lemma avn_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 AVN_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 SHB)
                       (Z_to_bv 64 136) (Z_to_bv 64 AVPM_FILE) (Z_to_bv 64 358) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells asegs m1 (bv_unsigned sp + -32) (avn_frame j s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_X509_VERIFY_PARAM_new) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros GSB SHB0 ST CEIL LO MI. acb. unfold P_X509_VERIFY_PARAM_new, P_CRYPTO_zalloc, AVN_RA, R_X509_VERIFY_PARAM_new_CRYPTO_zalloc, AVPM_FILE, SHB.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    do 5 step. step. step. step. do 6 step. finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma avn_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (j : list byte),
      0 < A -> A + 136 <= bv_unsigned sp + -32 -> (A + 136 <= ALOWSH_LO \/ AHI_LO <= A) ->
      accessible m A 136 ->
      rw_cells asegs m A vpm_zero_cells ->
      rw_cells asegs m (bv_unsigned sp + -32) (avn_frame j s1 s0 ra) -> mem_inv asegs m -> A mod 16 = 0 ->
      evt asegs (fun ms' => exists m1 (a1x a2x a3x : word),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1x a2x a3x a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(A, A + 136)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 A vpm_new_cells)
        (MS (mkR (Z_to_bv 64 AVN_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 SHB) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AVN_RA)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HA HS NS ACC0 BLK FR MI A16. unfold AVN_RA, R_X509_VERIFY_PARAM_new_CRYPTO_zalloc, SHB.
    replace (ret_pc (Z_to_bv 64 0x432314)) with (Z_to_bv 64 0x432314) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. unfold vpm_zero_cells, wz in BLK. unfold avn_frame in FR. unfold vpm_new_cells.
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(A, A + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(A, A + 136)]) by (constructor; [cbn; exact NS| constructor]).
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m A 136)) in ACC'.
    Local Ltac reacc ACC' MU NSW := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx _ 136) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    (* [comment removed for export] *)
    reacc ACC' MU NSW. step. ubal_by A16. step. if_lit. zstep. zstep. zstep. ck8_check ACC (A + 36). clear ACC. st1.
    (* [comment removed for export] *)
    reacc ACC' MU NSW. zstep. zstep. zstep. ck8_check ACC (A + 40). clear ACC. step. zstep. st1.
    (* [comment removed for export] *)
    reacc ACC' MU NSW. zstep. zstep. ck8_check ACC (A + 44). clear ACC. st1.
    (* [comment removed for export] *)
    do 5 step. finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma avpmnew_spec : vpmnew_stmt H.
  Proof.
    unfold vpmnew_stmt. intros until CH.
    intros VIS HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM RAE.
    unfold VPMNEW_STACK, FR_X509_VERIFY_PARAM_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK in LO.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    unfold VPM_SIZE in *.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply avn_seg1 with (lo := lo); [exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)])
      by (constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 v) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (XP1 : xpres H LB (bv_unsigned sp) memflag_foot m m1)
      by (eapply (xpres_of_munch H s LB _ memflag_foot _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold avn_frame in FR2.
      change ([CB 8 j; C8 s1; C8 s0; C8 ra]) with ([CB 8 j; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -32 + 16) by lia.
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -32 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (SP16' : (bv_unsigned sp + -32) mod 16 = 0) by (replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SP16; reflexivity).
    clear CW AW.
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 136) (size := 1) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| reflexivity| reflexivity| ..]; rewrite ?Z.mul_1_r; rewrite ?unsigned_lit by (unfold AVN_RA, R_X509_VERIFY_PARAM_new_CRYPTO_zalloc; lia).
      all: first [exact HP1| exact KREL1| exact AUX1| exact ST1| exact CEIL| exact ERR1| exact MI1| reflexivity| exact SP16'| exact AC1| exact CH1| exact CHS1
                 | exact MF1| exact IM1| exact GM1| lia | unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                 | unfold AVN_RA; eapply pf_ok_call; [exact PF|]; unfold PF_vpmnew; intros y Hy; exact Hy
                 | match goal with |- ?G => idtac "LEFT:" G end]. }
    intros [msF2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO. rewrite ?Z.mul_1_r in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & ADDR & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4.
    pose proof (aapp_bounds A 136 BR7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    apply vpm_zero_recut in BLK.
    assert (ACC2 : accessible m2 A 136) by (eapply addressable_accessible; [exact ADDR| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    eapply (ahh_evt H HH); [exact KREL2| exact VIS2| eapply avn_seg2; [lia| lia| exact (aapp_not_shadowland _ _ BR7)| exact ACC2| exact BLK| exact FR1| exact MI2| exact BR2]|].
    intros msF3 mo3 KREL3 MP3 (m3 & a1x & a2x & a3x & VIS3 & MU3 & WM3 & MI3 & HDR3).
    assert (CW3 : Forall (aclient_write_ok H ((p, A, 136) :: LB)) [(A, A + 136)]).
    { constructor; [| constructor]. right; right; left. exists (p, A, 136). split; [left; reflexivity| cbn; lia]. }
    unfold vpmnew_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, a1x, a2x, a3x, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, A, p, s'.
    split; [exact VIS3|]. split; [exact KREL3|].
    split; [eapply (ah_mpres_trans H HH); [| exact MP3]; eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI3|].
    split. { eapply ACONST_frame; [exact AC2| exact MU3| exact WM3|]. constructor; [eapply aconst_ok_aapp; [exact BR7| cbn; lia| cbn; lia]| constructor]. }
    split. { apply (stk_transport_disjoint asegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
             apply (rw_cells_transport asegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
             unfold avn_frame in FR3. eapply stk_release in FR3; [| exact ST3| lia]. cbn [cells_size csize Nat.add] in FR3.
             replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in FR3 by lia. exact FR3. }
    split. { rewrite unsigned_lit in * by (unfold ATP; lia). eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; lia]. }
    split. { eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3| exact CW3]. }
    split. { eapply xpres_trans; [exact XP1|]. eapply xpres_trans.
             - eapply (xpres_weaken H LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto].
             - eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|]. constructor; [right; left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (ah_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3| exact CW3]. }
    split. { unfold VPMobj. split; [apply (vpm_new_recut _ _ p) in HDR3; exact HDR3|]. split; [left; reflexivity|]. cbn. reflexivity. }
    split.
    { unfold VPM_shad, VPM_SIZE. split; [unfold AAPP_HI; lia|]. split; [| exact I].
      eapply addressable_transport; [exact ADDR| exact MU3| exact WM3|].
      pose proof (sh_aapp_range A 136 BR7 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3.
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1.
      cbn. destruct BR7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    split; [eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]|].
    exact AL2.
  Qed.
End W.
