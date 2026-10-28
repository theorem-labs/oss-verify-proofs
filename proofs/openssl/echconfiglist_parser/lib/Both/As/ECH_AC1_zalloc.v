(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1
  ECH_AKit ECH_AC1_malloc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition ACZ_RA1 : Z := R_CRYPTO_zalloc_CRYPTO_malloc.   (* [comment removed for export] *)
  Definition ACZ_RA2 : Z := R_CRYPTO_zalloc_asan_memset.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition acz_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition acz1_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 : word)
      (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR (Z_to_bv 64 ACZ_RA1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 n)
                   (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -32)
      /\ rw_cells asegs m1 (bv_unsigned sp + -32) (acz_frame s2 s1 s0 ra).

  Lemma acz_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (n lo : Z),
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (acz1_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 F fc n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. acb. unfold P_CRYPTO_zalloc, P_CRYPTO_malloc.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    do 8 step. unfold acz1_post, ACZ_RA1, R_CRYPTO_zalloc_CRYPTO_malloc. finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma acz_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n : Z),
      0 < A < 2^64 -> 0 <= n < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 ACZ_RA2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 n)
                                         (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                                         (Z_to_bv 64 A) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 AASAN_MEMSET) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ACZ_RA1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 n) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ACZ_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until n. intros HA HN MI. unfold ACZ_RA1, ACZ_RA2, R_CRYPTO_zalloc_CRYPTO_malloc, R_CRYPTO_zalloc_asan_memset, AASAN_MEMSET.
    replace (ret_pc (Z_to_bv 64 0x1f096c)) with (Z_to_bv 64 0x1f096c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR.
    step. step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 4 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma acz_seg3 :
    forall (sp gp tp t0 t1 t2 s0x s1x a0x a1 a2 a3 a4 a5 a6 a7 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z),
      0 < A < 2^64 ->
      rw_cells asegs m (bv_unsigned sp + -32) (acz_frame s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (ret_pc ra) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ACZ_RA2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x s1x a0x a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 A) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ACZ_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until A. intros HA FR MI. unfold ACZ_RA2, R_CRYPTO_zalloc_asan_memset.
    replace (ret_pc (Z_to_bv 64 0x1f0984)) with (Z_to_bv 64 0x1f0984) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold acz_frame in FR.
    do 7 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition acarr_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (target ns : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ns) a2 a3 (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 target) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp).

  Lemma acarr_zalloc_prefix :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (num size lo : Z),
      0 <= num < 2^32 -> 0 <= size < 2^32 -> 1 <= num * size <= 2^28 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (acarr_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc P_CRYPTO_zalloc (num * size) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 num) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_calloc) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HN HS HNS ST CEIL LO MI. acb. unfold P_CRYPTO_calloc, P_CRYPTO_zalloc.
    pose proof (word_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    do 7 step; zstep; rewrite (Z.shiftr_div_pow2 _ 64), Z.div_small by lia.
    step; step; if_true; zstep; do 8 step.
    lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => release_frame FR ST (bv_unsigned sp) end. unfold acarr_post. finish.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma czalloc_post_back : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc s LB n lo B m m1 mo c,
    xpres H LB (bv_unsigned sp) memflag_foot m m1 ->
    czalloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m1 mo c ->
    czalloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m mo c.
  Proof.
    intros until c. intros XP PO. unfold czalloc_post in *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s' & E & REST).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, p, s'. split; [exact E|].
    repeat match goal with |- _ /\ _ => split end; try tauto.
    eapply xpres_trans; [exact XP| tauto].
  Qed.

  Lemma aczalloc_spec : czalloc_stmt H.
  Proof.
    unfold czalloc_stmt, czalloc_stmt_gen. intros until CH.
    intros VIS A0 SZ HN HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM.
    subst size. rewrite Z.mul_1_r in *.
    unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK in LO. acb. subst a0. subst tp.
    rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply acz_seg1; try eassumption; lia|].
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
      pose proof FR1 as FR2. unfold acz_frame in FR2.
      change ([C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -32 + 16) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    (* [comment removed for export] *)
    pose proof (acmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (ah_seq H HH).
    { eapply CM with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (n := num) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try (unfold CMALLOC_STACK, FR_CRYPTO_malloc, AMALLOC_STACK; lia).
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
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_czalloc; intros x Hx; exact Hx
           | |- _ <= as_AL _ _ => exact HAL
           | |- MEMFLAG _ _ => exact MF1
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- ?G => idtac "LEFT:" G
           end. }
    intros [msF2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p & s' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & ADDR & MF2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4.
    pose proof (aapp_bounds A num BR7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply acz_seg2; [lia| lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3|..].
    { eapply (asan_memset_specZ H HH) with (lo := lo); try eassumption; try lia.
      - eapply addressable_accessible; [exact ADDR| lia| lia| unfold AAPP_HI; lia].
      - exact (ah_blk_shvis H HH _ _ _ _ _ _ HEAP2 (or_introl eq_refl)).
      - eapply aapp_in_app_mem; [exact BR7| lia| lia].
      - eapply aconst_ok_aapp; [exact BR7| lia| lia]. }
    intros msF4 mo4 KREL4 MP4 PO. unfold amemset_postZ in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m3 & VIS4 & MU3 & WM3 & MI3 & ST3 & BLK3 & AC3).
    assert (CW3 : Forall (aclient_write_ok H ((p, A, num) :: LB)) [(A, A + num); (bv_unsigned sp + -32 - 4096, bv_unsigned sp + -32)]).
    { constructor; [| constructor; [left; cbn; lia| constructor]]. right; right; left. exists (p, A, num). split; [left; reflexivity| cbn; lia]. }
    assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -32) (acz_frame s2 s1 s0 ra)).
    { eapply (rw_cells_transport asegs _ m2 m3); [exact FR1| exact MU3| exact WM3|]. cbn. lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt H HH); [exact KREL4| exact VIS4| eapply acz_seg3; [lia| exact FR3| exact MI3]|].
    intros msF5 mo5 KREL5 MP5 VIS5.
    unfold czalloc_post. cbn [cfg_ms cfg_model].
    exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m3, errv2, A, p, s'.
    split; [exact VIS5|]. split; [exact KREL5|].
    split; [eapply (ah_mpres_trans H HH); [| exact MP5]; eapply (ah_mpres_trans H HH); [| exact MP4]; eapply (ah_mpres_trans H HH); [| exact MP3];
            eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI3|]. split; [exact AC3|].
    split. { unfold acz_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
    split. { rewrite unsigned_lit by (unfold ATP; lia). eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; lia]. }
    split. { eapply (ah_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3| exact CW3]. }
    split.
    { eapply xpres_trans; [exact XP1|]. eapply xpres_trans.
      - eapply (xpres_weaken H LB LB _ _ memflag_foot); [exact XP2| lia| auto| auto].
      - eapply (xpres_of_munch_fresh H HH); [exact HEAP2| lia| exact MU3| exact WM3|].
        constructor; [right; left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
    split; [exact BR|].
    split. { eapply (ah_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3| exact CW3]. }
    split. { exact BLK3. }
    split. { eapply addressable_transport; [exact ADDR| exact MU3| exact WM3|].
             pose proof (sh_aapp_range A num BR7 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3.
             assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. rewrite S0 in S1.
             cbn. destruct BR7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
    split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
    split; [eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]|].
    exact AL2.
  Qed.

  Lemma accalloc_spec : ccalloc_stmt H.
  Proof.
    unfold ccalloc_stmt, czalloc_stmt_gen. intros until CH.
    intros VIS A0 (A1 & HN & HS) HNS HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL MF IM GM.
    unfold CARRAY_STACK, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK in LO.
    acb. subst a0 a1. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply acarr_zalloc_prefix; [exact HN| exact HS| exact HNS| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (XP1 : xpres H LB (bv_unsigned sp) memflag_foot m m1).
    { eapply (xpres_of_munch H s LB _ memflag_foot _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    pose proof aczalloc_spec as CZ. unfold czalloc_stmt, czalloc_stmt_gen in CZ.
    subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    eapply (ah_mono H HH).
    { eapply CZ with (size := 1) (v := v) (CH := CH) (lo := lo) (B := B) (LB := LB) (s := s); [exact VIS1| reflexivity| reflexivity| ..]; rewrite ?Z.mul_1_r.
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]
           | |- as_chain _ _ _ _ => eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]
           | |- forall fp' ra', In _ _ -> _ => exact CHS
           | |- pf_ok _ _ _ _ => exact PF
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           | |- _ => first [assumption | lia | unfold CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                              | match goal with |- ?G => idtac "LEFT:" G end]
           end. }
    intros c PO. eapply czalloc_post_back; [exact XP1|]. rewrite Z.mul_1_r in PO.
    unfold czalloc_post in PO |- *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & p & s' & E & K2 & MP2 & REST).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, p, s'. split; [exact E|]. split; [exact K2|].
    split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]| exact REST].
  Qed.
End W.
