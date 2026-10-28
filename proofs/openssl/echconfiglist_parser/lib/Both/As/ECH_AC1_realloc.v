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

  Definition ACR_RA : Z := R_CRYPTO_realloc_realloc.   (* [comment removed for export] *)
  Definition ACR_A2 : Z := 0x5e8cc0.                    (* [comment removed for export] *)

  Local Ltac prep_statics IM GM :=
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_aligned_alloc,
      P_CRYPTO_realloc, P_CRYPTO_free, wz in IM, GM.

  (* [comment removed for export] *)
  Definition acr1_post (sp gp tp t0 t1 t2 a2 a3 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
      (F : bvmap 5 word) (fc : bv 32) (A num lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1 j,
      ms' = MS (mkR (Z_to_bv 64 ACR_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a3
                   (Z_to_bv 64 A) (Z_to_bv 64 num) (Z_to_bv 64 ACR_A2) a3 (Z_to_bv 64 P_CRYPTO_realloc) a5 a6 a7
                   a2 (Z_to_bv 64 num) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AREALLOC_STUB) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells asegs m1 (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra)
      /\ IMPL_mem m1 /\ GOT_mem m1.

  Lemma acr_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A num lo : Z),
      0 < A < 2^64 -> 1 <= num < 2^32 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
      IMPL_mem m -> GOT_mem m ->
      evt asegs (acr1_post sp gp tp t0 t1 t2 a2 a3 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 F fc A num lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 num) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_realloc) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros HA HN ST CEIL LO MI IM GM. acb.
    unfold P_CRYPTO_realloc, AREALLOC_STUB in *. prep_statics IM GM. destruct IM as (IM1 & IM2 & IM3).
    pose proof (aword_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    do 14 step. step. try if_true.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. step.
    unfold acr1_post, ACR_RA, ACR_A2, R_CRYPTO_realloc_realloc. finish.
    - lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => exact FR end.
    - unfold IMPL_mem, A_malloc_impl, A_realloc_impl, A_free_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma acr_seg2 :
    forall (sp gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (j : list byte),
      0 < A < 2^64 ->
      rw_cells asegs m (bv_unsigned sp + -48) (cm_frame j s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (ret_pc ra) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 ACR_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ACR_RA)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HA FR MI. unfold ACR_RA, R_CRYPTO_realloc_realloc.
    replace (ret_pc (Z_to_bv 64 0x1f0d2c)) with (Z_to_bv 64 0x1f0d2c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. unfold cm_frame in FR.
    step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    do 8 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition acrarr_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (v lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists m1,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 v) a3 a4 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_realloc) fc None m1 (seg_rom asegs)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp).

  Lemma acrarr_prefix :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (num size lo : Z),
      0 <= num < 2^32 -> 0 <= size < 2^32 -> 1 <= num * size < 2^32 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (acrarr_post ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (num * size) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 num) (Z_to_bv 64 size) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_CRYPTO_realloc_array) fc None m (seg_rom asegs)).
  Proof.
    unfold P_CRYPTO_realloc_array, P_CRYPTO_realloc. intros until lo; intros HN HS HP ST CEIL LO MI. acb.
    pose proof (aword_range sp) as SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 32%nat ST.
    do 8 step. zstep. rewrite (Z.shiftr_div_pow2 _ 64), Z.div_small by lia.
    step. if_true. zstep. do 8 step.
    release_frame FR ST (bv_unsigned sp). unfold acrarr_post. finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Let HRE : realloc_stmt H := proj1 (proj2 HHx).

  Lemma crealloc_post_back : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc s LB p old n obs lo B m m1 mo c,
    xpres H (as_lb_remove H p LB) (bv_unsigned sp) [] m m1 ->
    crealloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p old n obs lo B m1 mo c ->
    crealloc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p old n obs lo B m mo c.
  Proof.
    intros until c. intros XP PO. unfold crealloc_post in *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A & junk & p' & s' & E & REST).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A, junk, p', s'. split; [exact E|].
    repeat match goal with |- _ /\ _ => split end; try tauto.
    eapply xpres_trans; [exact XP| tauto].
  Qed.

  Lemma acrealloc_spec : crealloc_stmt H.
  Proof.
    unfold crealloc_stmt, crealloc_stmt_gen. intros until CH.
    intros VIS A0 A1 SZ HN HOLD HP KREL HIN OBS LEN BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL ADDR IM GM.
    subst size. rewrite Z.mul_1_r in *.
    unfold CREALLOC_STACK, FR_CRYPTO_realloc, AREALLOC_STACK, AREALLOC_MAX in *. acb. subst a0 a1 tp.
    rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ah_blocks H HH _ _ _ _ HP HIN) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *. unfold AIMG_TOP in B4.
    pose proof (aapp_bounds A old B7 B3) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    unfold zlength in LEN.
    assert (SUB : forall b, In b (as_lb_remove H p LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply acr_seg1; try eassumption; lia|].
    intros msF1 mo1 KREL1 MP1 (m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & IM1 & GM1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -48, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -48, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (OBS1 : rw_cells asegs m1 A [CB (Z.to_nat old) obs]).
    { eapply (rw_cells_transport asegs _ m m1); [exact OBS| exact MU1| exact WM1|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. lia. }
    assert (ADDR1 : addressable m1 A old).
    { eapply addressable_transport; [exact ADDR| exact MU1| exact WM1|].
      pose proof (sh_aapp_range A old B7 B3) as (S1 & S2 & S3). unfold AHI_LO in S3. cbn. lia. }
    destruct ADDR1 as [Hold0 SH1].
    (* [comment removed for export] *)
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold cm_frame in FR2.
      change ([CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 j; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -48 + 32) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    (* [comment removed for export] *)
    pose proof HRE as RE. unfold realloc_stmt, realloc_stmt_at in RE.
    eapply (ah_seq H HH).
    { eapply RE with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (A := A) (old := old) (n := num) (bs := obs) (sbs := shadow_of old)
                     (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- In _ _ => exact HIN
           | |- as_alloc_ok _ _ _ _ => eapply (ah_alloc H HH); [exact HP1| lia| lia| lia]
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- rw_cells _ _ _ [CB _ _] => exact OBS1
           | |- SHAD _ _ _ => exact SH1
           | |- Z.of_nat (length (shadow_of ?k)) = nsh ?k => apply shadow_of_length; lia
           | |- mem_inv _ _ => exact MI1
           | |- ACONST _ => exact AC1
           | |- as_chain _ _ _ _ => exact CH1
           | |- trace_ok _ _ _ => cbn [map snd]; exact (pf_ok_site _ _ _ _ _ _ PF (or_introl eq_refl))
           | |- _ <= as_AL _ _ => exact HAL
           | |- _ => first [lia | unfold AREALLOC_STACK; lia | match goal with |- ?G => idtac "LEFT:" G end]
           end. }
    intros [msF2 mo2] PO. unfold realloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A' & junk & p' & s' &
                    VIS2 & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HPRES & BR & HEAP2 & BLK & ADDR2 & AC2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, HPRES by lia.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7).
    apply (apres_rw_cells H _ _ _ _ _ _ HPRES) in FR1; [| left; cbn; lia].
    (* [comment removed for export] *)
    eapply (ahh_evt H HH); [exact KREL2| exact VIS2| eapply acr_seg2; [lia| exact FR1| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3.
    unfold crealloc_post. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A', junk, p', s'.
    split; [exact VIS3|]. split; [exact KREL3|]. split; [eapply (ah_mpres_trans H HH); [| exact MP3]; eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI2|]. split; [exact AC2|].
    split. { unfold cm_frame in FR1. release_frame FR1 ST2 (bv_unsigned sp). exact ST2. }
    split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR2|]. split; [exact AUX2|].
    split.
    { eapply xpres_trans.
      - eapply (xpres_weaken H LB (as_lb_remove H p LB) (bv_unsigned sp) (bv_unsigned sp) [] []);
          [eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|] | lia | exact SUB | auto].
        constructor; [left; cbn; lia| constructor].
      - eapply (xpres_weaken H _ _ _ _ [] []); [apply xpres_of_apres; exact HPRES| lia| auto| auto]. }
    split; [exact BR|]. split; [exact HEAP2|]. split; [exact BLK|]. split; [exact ADDR2|].
    split; [eapply (IMPL_apres H); [exact HPRES| exact IM1]|].
    split; [eapply (GOT_apres H); [exact HPRES| exact GM1]|].
    exact AL2.
  Qed.

  Lemma acrealloc_array_spec : crealloc_array_stmt H.
  Proof.
    unfold crealloc_array_stmt, crealloc_stmt_gen. intros until CH.
    intros VIS A0 A1 (A2 & HN & HS) HNS HOLD HP KREL HIN OBS LEN BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL ADDR IM GM.
    unfold CREALLOC_ARRAY_STACK, CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, AREALLOC_STACK, AREALLOC_MAX in *.
    acb. subst a0 a1 a2 tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (SUB : forall b, In b (as_lb_remove H p LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    pose proof (ah_blocks H HH _ _ _ _ HP HIN) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *. unfold AIMG_TOP in B4.
    pose proof (aapp_bounds A old B7 B3) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    unfold zlength in LEN.
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply acrarr_prefix; [exact HN| exact HS| lia| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [left; cbn; lia| constructor]. }
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)]).
    { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]. }
    assert (XP1 : xpres H (as_lb_remove H p LB) (bv_unsigned sp) [] m m1).
    { eapply (xpres_weaken H LB (as_lb_remove H p LB) (bv_unsigned sp) (bv_unsigned sp) [] []);
        [eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|] | lia | exact SUB | auto].
      constructor; [left; cbn; lia| constructor]. }
    pose proof acrealloc_spec as CR. unfold crealloc_stmt, crealloc_stmt_gen in CR.
    eapply (ah_mono H HH).
    { eapply CR with (A := A) (size := 1) (CH := CH) (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (old := old) (obs := obs);
        [exact VIS1| reflexivity| reflexivity| reflexivity| ..]; rewrite ?Z.mul_1_r.
      all: lazymatch goal with
           | |- as_RHEAP _ _ _ _ => eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]
           | |- as_AKREL _ _ _ => exact KREL1
           | |- In _ _ => exact HIN
           | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]
           | |- rw_cells _ _ _ [CB _ _] => eapply (rw_cells_transport asegs _ m m1); [exact OBS| exact MU1| exact WM1| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia]
           | |- zlength _ = _ => unfold zlength; exact LEN
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => reflexivity
           | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]
           | |- as_chain _ _ _ _ => eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]
           | |- forall fp' ra', In _ _ -> _ => exact CHS
           | |- pf_ok _ _ _ _ => exact PF
           | |- addressable _ _ _ => eapply addressable_transport; [exact ADDR| exact MU1| exact WM1|];
                                     pose proof (sh_aapp_range A old B7 B3) as (S1 & S2 & S3); unfold AHI_LO in S3; cbn; lia
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           | |- _ => first [assumption | lia | unfold CREALLOC_STACK, FR_CRYPTO_realloc, AREALLOC_STACK; lia | match goal with |- ?G => idtac "LEFT:" G end]
           end. }
    intros c PO. eapply crealloc_post_back; [exact XP1|]. rewrite Z.mul_1_r in PO.
    unfold crealloc_post in PO |- *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A' & junk & p' & s' & E & K2 & MP2 & REST).
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, A', junk, p', s'. split; [exact E|]. split; [exact K2|].
    split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]| exact REST].
  Qed.
End W.
