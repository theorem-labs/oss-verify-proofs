(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C6 ECH_AKit ECH_AsKit ECH_AC1_zalloc ECH_AC1_free.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition ABN_RA : Z := R_BUF_MEM_new_CRYPTO_zalloc.   (* [comment removed for export] *)
  Definition ABUF_FILE : Z := 0x72e20.                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition abn_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma rw_cells_recut : forall m A cs cs',
    rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
  Proof.
    intros m A cs cs' [[WF B] W] WF' E. split; [split; [exact WF'| rewrite E; exact B]|].
    rewrite <- (cells_bytes_length cs' WF'), E, (cells_bytes_length cs WF). exact W.
  Qed.
  (* [comment removed for export] *)
  Lemma rw_cells_as_CB : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
  Proof.
    intros m A cs RC. pose proof RC as [[WF _] _]. eapply rw_cells_recut; [exact RC| |].
    - cbn. split; [apply cells_bytes_length; exact WF| exact I].
    - cbn. rewrite app_nil_r. reflexivity.
  Qed.
  Lemma buf_zero_recut : forall m A, rw_cells asegs m A [CB (Z.to_nat 32) (zeros (Z.to_nat 32))] -> rw_cells asegs m A (buf_cells (mkBUF 0 0 0 0)).
  Proof. intros m A HB. eapply rw_cells_recut; [exact HB| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition abn1_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 ABN_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 0)
                   (Z_to_bv 64 32) (Z_to_bv 64 ABUF_FILE) (Z_to_bv 64 35) a3 a4 a5 a6 a7 (Z_to_bv 64 ASHADOW_BASE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -32)
      /\ rw_cells asegs m1 (bv_unsigned sp + -32) (abn_frame s2 s1 s0 ra).

  Lemma abn_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      ACONST m -> stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (abn1_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BUF_MEM_new) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros AC ST CEIL LO MI. acb. unfold P_BUF_MEM_new, P_CRYPTO_zalloc.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ACONST_shbase _ AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    do 6 step.                        (* [comment removed for export] *)
    step. step. step.                 (* [comment removed for export] *)
    do 5 step. step.                  (* [comment removed for export] *)
    unfold abn1_post, ABN_RA, R_BUF_MEM_new_CRYPTO_zalloc, ABUF_FILE. finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma abn_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A lo : Z),
      0 < A -> A mod 16 = 0 -> A + 32 <= aceil -> aceil <= lo -> accessible m A 32 ->
      rw_cells asegs m A (buf_cells (mkBUF 0 0 0 0)) ->
      rw_cells asegs m (bv_unsigned sp + -32) (abn_frame s2 s1 s0 ra) -> stk asegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 (A + 24)) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(A + 24, A + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
          /\ rw_cells asegs m1 A (buf_cells (mkBUF 0 0 0 0)))
        (MS (mkR (Z_to_bv 64 ABN_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 0) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHADOW_BASE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ABN_RA)) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HA HAL HC CEIL ACC0 BLK FR ST LO MI. unfold ABN_RA, R_BUF_MEM_new_CRYPTO_zalloc.
    replace (ret_pc (Z_to_bv 64 0x24b964)) with (Z_to_bv 64 0x24b964) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold buf_cells, wz in BLK. cbn [bm_len bm_data bm_max bm_flags] in BLK. unfold abn_frame in FR. rewrite ASHADOW_BASE_val.
    pose proof (munch_refl [(A + 24, A + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC. clear ACC0.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. ubal_by HAL. step. if_lit.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACC (A + 24).
    st1. do 6 step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma abf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo len mx fl : Z),
      rw_cells asegs m a (buf_cells (mkBUF len 0 mx fl)) -> 0 < a -> a mod 16 = 0 -> a + 32 <= aceil -> accessible m a 32 -> aapp a 32 ->
      0 <= len < 2^64 -> 0 <= mx < 2^64 -> 0 <= fl < 2^64 ->
      ACONST m -> stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 ABUF_FILE) (Z_to_bv 64 51) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp)
          /\ rw_cells asegs m1 a (buf_cells (mkBUF len 0 mx fl)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BUF_MEM_free) fc None m (seg_rom asegs)).
  Proof.
    intros until fl. intros BC POS PAL BL ACC0 AP LR MR FLR AC ST CEIL LO MI. unfold P_BUF_MEM_free, P_CRYPTO_free, ABUF_FILE.
    unfold buf_cells, wz in BC. cbn [bm_len bm_data bm_max bm_flags] in BC.
    pose proof (rw_cells_bound _ _ _ _ BC) as BB. cbn [cells_size csize Nat.add] in BB.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ACONST_shbase _ AC) as [GSB SHB]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB. rewrite ASHADOW_BASE_val in SHB.
    pose proof (aapp_not_shadowland _ _ AP) as NS1.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 32)) in ACC'.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 5 step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 32) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|];
        constructor; [cbn; unfold AHI_LO in *; lia| constructor]) end.
    clear ACC'.
    (* [comment removed for export] *)
    step. step. ubal_by PAL. step. if_lit. step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 8).
    st1. step. if_lit.
    (* [comment removed for export] *)
    step. step. step. step. st1. st1. st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma abufnew_spec : bufnew_stmt H.
  Proof.
    unfold bufnew_stmt. intros until CH.
    intros VIS A0 HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM.
    unfold BUFNEW_STACK, FR_BUF_MEM_new, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK, BUFMEM_SIZE in *.
    acb. subst a0. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply abn_seg1; [exact AC| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)]).
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
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold abn_frame in FR2.
      change ([C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -32 + 16) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    (* [comment removed for export] *)
    pose proof (aczalloc_spec H HH) as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    eapply (ah_seq H HH).
    { eapply CZ with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 32) (size := 1) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK; lia).
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ mod 16 = 0 => rewrite <- Zminus_mod_idemp_l; rewrite <- Zminus_mod_idemp_l in SP16 || idtac; replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia;
                                rewrite Zminus_mod, SP16; reflexivity
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CH1
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_bufnew; intros x Hx; exact Hx
           | |- _ <= as_AL _ _ => exact HAL
           | |- MEMFLAG _ _ => exact MF1
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- ?G => idtac "LEFT:" G
           end. }
    intros [msF2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & ADDR & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4.
    pose proof (aapp_bounds A 32 BR7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    pose proof (buf_zero_recut _ _ BLK) as BLKc.
    assert (ACC2 : accessible m2 A 32) by (eapply addressable_accessible; [exact ADDR| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    eapply (ahh_evt H HH); [exact KREL2| exact VIS2| eapply abn_seg2 with (lo := lo); [lia| lia| lia| exact CEIL| exact ACC2| exact BLKc| exact FR1| exact ST2| lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (m3 & VIS3 & MU3 & WM3 & MI3 & ST3 & BLK3).
    assert (CW3 : Forall (aclient_write_ok H ((p, A, 32) :: LB)) [(A + 24, A + 32)]).
    { constructor; [| constructor]. right; right; left. exists (p, A, 32). split; [left; reflexivity| cbn; lia]. }
    unfold bufnew_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, (Z_to_bv 64 (A + 24) : word), (Z_to_bv 64 0 : word), b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, A, p, s'.
    split; [exact VIS3|]. split; [exact KREL3|].
    split; [eapply (ah_mpres_trans H HH); [| exact MP3]; eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI3|].
    split. { eapply ACONST_frame; [exact AC2| exact MU3| exact WM3|]. constructor; [| constructor]. eapply aconst_ok_aapp; [exact BR7| cbn; lia| cbn; lia]. }
    split; [exact ST3|].
    split. { rewrite unsigned_lit by (unfold ATP; lia). eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; lia]. }
    split. { eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3| exact CW3]. }
    split.
    { eapply xpres_trans; [exact XP1|]. eapply xpres_trans.
      - eapply (xpres_weaken H LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto].
      - eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|].
        constructor; [right; left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (ah_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3| exact CW3]. }
    split. { exact BLK3. }
    split. { eapply addressable_transport; [exact ADDR| exact MU3| exact WM3|].
             pose proof (sh_aapp_range A 32 BR7 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3.
             assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1.
             cbn. unfold BUFMEM_SIZE in *. destruct BR7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    split; [eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]|].
    exact AL2.
  Qed.

  Lemma abuffree_spec : buffree_stmt H.
  Proof.
    unfold buffree_stmt. intros until CH.
    intros VIS A0 HIN BC ADDR LR MR FLR HP KREL AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL IM GM.
    unfold BUFFREE_STACK, FR_BUF_MEM_free, CFREE_STACK, AFREE_STACK, BUFMEM_SIZE in *.
    acb. subst a0. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ah_blocks H HH _ _ _ _ HP HIN) as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). cbn [blk_addr blk_size fst snd] in BR1, BR2, BR3, BR4, BR5, BR6, BR7. unfold AIMG_TOP in BR4.
    pose proof (aapp_bounds A 32 BR7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    assert (ACC0 : accessible m A 32) by (eapply addressable_accessible; [exact ADDR| lia| lia| unfold AAPP_HI; lia]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply abf_seg1 with (lo := lo); [exact BC| lia| lia| lia| exact ACC0| exact BR7| exact LR| exact MR| exact FLR| exact AC| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & BC1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (ADDR1 : addressable m1 A 32).
    { eapply addressable_transport; [exact ADDR| exact MU1| exact WM1|].
      pose proof (sh_below_aceil (A + 32 + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
      unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. cbn. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    assert (CH1 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_seq H HH).
    pose proof (rw_cells_as_CB _ _ _ BC1) as BCB. cbn [cells_size csize Nat.add] in BCB. change 32%nat with (Z.to_nat 32) in BCB.
    { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (A := A) (n := 32) (CH := CH) (errv := errv) (bs := cells_bytes (buf_cells (mkBUF len 0 mx fl)));
        [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CFREE_STACK, AFREE_STACK; lia).
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- In _ _ => exact HIN
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
    apply (ah_done H HH). unfold buffree_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s'.
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
