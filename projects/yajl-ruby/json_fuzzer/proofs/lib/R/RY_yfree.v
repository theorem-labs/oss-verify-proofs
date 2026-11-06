(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlParser YajlLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma perm_yfree_bs : forall (A : Type) (HD bs : A) (LX BB REST : list A),
  Permutation ((HD :: LX ++ BB ++ [bs]) ++ REST) (bs :: (HD :: LX ++ BB) ++ REST).
Proof.
  intros. symmetry. change (bs :: (HD :: LX ++ BB) ++ REST) with (bs :: ((HD :: LX ++ BB) ++ REST)).
  replace ((HD :: LX ++ BB ++ [bs]) ++ REST) with ((HD :: LX ++ BB) ++ bs :: REST); [apply Permutation_middle|].
  cbn. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma perm_yfree_buf : forall (A : Type) (HD : A) (LX BB REST : list A),
  Permutation ((HD :: LX ++ BB) ++ REST) (BB ++ (HD :: LX) ++ REST).
Proof.
  intros. change ((HD :: LX ++ BB) ++ REST) with (((HD :: LX) ++ BB) ++ REST). rewrite <- app_assoc. apply Permutation_app_swap_app.
Qed.
Lemma perm_yfree_lex : forall (A : Type) (HD : A) (LX REST : list A),
  Permutation ((HD :: LX) ++ REST) (LX ++ HD :: REST).
Proof. intros. cbn. apply Permutation_middle. Qed.

Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YWF : ywrap_free_stmt HK.
Hypothesis YBF : ybuf_free_stmt HK.
Hypothesis YLF : ylex_free_stmt HK.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

Section Fn.
Variables (REST : list block) (h : yhandle) (mh : mhand) (lo B : Z) (errv : word) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState),
  yfree_rpost HK sp tp m REST h mh lo B errv a0' m' mo' s' ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis TP : tp = wz RATP.
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RY_FREE_STACK.
Hypothesis SPB : bv_unsigned sp <= B.
Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
Hypothesis LO0 : 0 <= lo.

Let HDB : block := (mh_id mh, mh_addr mh, SIZEOF_HANDLE).
Let LX := lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h).
Let BB := buf_blocks (mh_decbuf mh) (h_decbuf h).

(* [comment removed for export] *)
Lemma yfree_tail : forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (errv1 pew pad : word),
  HK s1' ((HDB :: LX ++ BB) ++ REST) m1 mo1 -> ystatics m1 ->
  rw_cells rsegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk rsegs m1 lo (bv_unsigned sp + -16) -> mem_inv rsegs m1 -> rauxv_ok m1 B ->
  rw_cells rsegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells rsegs m1 (mh_addr mh) (hand_head_cells ryc h mh pew pad) -> rw_cells rsegs m1 (mh_addr mh + 72) (alloc_cells ryc) ->
  lexer_rep rsegs m1 (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72) ->
  buf_rep rsegs m1 (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (mh_addr mh)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz 0x13d08) fc None m1 (seg_rom rsegs)) mo1) K.
Proof.
  intros until pad. intros HK1 YS1 FR STK MI AX ERR PRES HH HA LR BR.
  unfold wz in *. pose proof LO as LO'. unfold RY_FREE_STACK, RY_LEX_FREE_STACK, RY_BUF_FREE_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
  destruct (HK_blocks HK HKB _ _ _ _ HK1) as [RNG SEP]. pose proof (HK_nodup HK HKB _ _ _ _ HK1) as ND.
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as HRG. unfold rblock_range, alloc_ceiling in HRG. cbn [blk_addr blk_size fst snd] in HRG.
  unfold hand_head_cells in HH. unfold alloc_cells in HA. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc] in HH, HA.
  unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, SIZEOF_HANDLE, wz in *. unfold RERRNO in ERR.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
  rz_seg HKS HK1.
  step. step.
  apply evt_done. clear MU WM.
  assert (HK1' : HK s1' (BB ++ (HDB :: LX) ++ REST) m1 mo1) by (eapply HKP; [exact HK1| apply perm_yfree_buf]).
  eapply (YBF ((HDB :: LX) ++ REST) (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72) lo B errv1 K);
    [ exact K0 | apply RYST_split; split; [exact HK1'| exact YS1] | exact BR | exact HA
    | exists HDB; split; [left; reflexivity| cbn; lia]
    | split; [exact AX|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_BUF_FREE_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR|]; split; [exact MI| exact TP]
    | reflexivity | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' POST.
  destruct POST as ((MI2 & STK2 & (errv2 & ERR2) & AX2 & HP2) & HA2 & RY2).
  replace (ret_pc (Z_to_bv 64 81168)) with (Z_to_bv 64 81168) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK2, HP2. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
  apply ry_pres_nil in HP2. apply RYST_split in RY2. destruct RY2 as [HK2 YS2]. change ((HDB :: LX) ++ REST) with (HDB :: LX ++ REST) in HK2, HP2.
  pose proof (ypres_frame _ _ _ _ _ _ HP2 FR ltac:(lia)) as FR2. clear FR.
  pose proof (ypres_block _ _ _ _ _ _ HP2 HH ltac:(exists HDB; split; [left; reflexivity| cbn; lia])) as HH2. clear HH.
  pose proof (lexer_rep_pres_sub _ _ _ _ _ _ _ _ (mh_lid mh) LR HP2 ltac:(intros x Hx; right; apply in_or_app; left; exact Hx)) as LR2. clear LR.
  assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
  { eapply ry_pres_trans; [exact PRES|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP2| lia| intros b0 Hb0; right; apply in_or_app; right; exact Hb0]. }
  unfold alloc_cells in HA2. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in HA2. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in HA2.
  clear HP2 MI STK ERR AX HK1 HK1' HA YS1 PRES BR.
  (* [comment removed for export] *)
  pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
  rz_seg HKS HK2.
  step. step.
  apply evt_done. clear MU WM.
  assert (HK2' : HK s2' (LX ++ HDB :: REST) m2 mo2) by (eapply HKP; [exact HK2| apply Permutation_middle]).
  eapply (YLF (HDB :: REST) (mh_lid mh) (mh_lexer mh) (mh_addr mh + 72) (mh_lexbuf mh) (h_lexer h) lo B errv2 K);
    [ exact K0 | apply RYST_split; split; [exact HK2'| exact YS2] | exact LR2 | exact HA2
    | exists HDB; split; [left; reflexivity| cbn; lia]
    | split; [exact AX2|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK2|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_LEX_FREE_STACK, RY_BUF_FREE_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR2|]; split; [exact MI2| exact TP]
    | reflexivity | ].
  cbv beta. intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 mo3 s3' POST.
  destruct POST as ((MI3 & STK3 & (errv3 & ERR3) & AX3 & HP3) & HA3 & RY3).
  replace (ret_pc (Z_to_bv 64 81176)) with (Z_to_bv 64 81176) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK3, HP3. rewrite (ry_errno_lit tp TP) in ERR3. unfold RERRNO in ERR3.
  apply ry_pres_nil in HP3. apply RYST_split in RY3. destruct RY3 as [HK3 YS3].
  pose proof (ypres_frame _ _ _ _ _ _ HP3 FR2 ltac:(lia)) as FR3. clear FR2.
  pose proof (ypres_block _ _ _ _ _ _ HP3 HH2 ltac:(exists HDB; split; [left; reflexivity| cbn; lia])) as HH3. clear HH2.
  assert (PRES3 : ry_pres REST (bv_unsigned sp) [] m m3).
  { eapply ry_pres_trans; [exact PRES2|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP3| lia| intros b0 Hb0; right; exact Hb0]. }
  unfold alloc_cells in HA3. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in HA3. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in HA3.
  clear HP3 MI2 STK2 ERR2 AX2 HK2 HK2' HA2 YS2 PRES2 LR2.
  pose proof (HK_nodup HK HKB _ _ _ _ HK3) as ND3.
  (* [comment removed for export] *)
  pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
  rz_seg HKS HK3.
  step. step. step. step. step. step. step.
  apply evt_done. release_frame FR3 STK3 (bv_unsigned sp).
  eapply YWF with (p := mh_id mh) (A := mh_addr mh) (n := 104);
    [exact K0 | exact HK3 | left; reflexivity | exact AX3 | lia | exact STK3 | exact CEIL
    | unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR3
    | exact MI3 | exact TP | reflexivity | ].
  cbv beta. intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x m4 mo4 s4' MI4 STK4 ERR4 AX4 HP4 HK4.
  rewrite (lb_remove_head HDB REST ND3) in HP4, HK4.
  eapply CONT. unfold yfree_rpost.
  split; [| apply RYST_split; split; [exact HK4| eapply ystatics_pres; [exact YS3| exact HP4]]].
  split; [exact MI4|]. split; [exact STK4|]. split; [eexists; exact ERR4|]. split; [exact AX4|].
  eapply ry_pres_trans; [exact PRES3|]. apply ry_pres_of_rheap_pres. exact HP4.
Qed.
End Fn.

Lemma yfree_spec : yfree_stmt HK.
Proof.
  unfold yfree_stmt. intros REST h mh lo B errv K. intros until s. intros K0 RY HR FP A0 CONT.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP]. pose proof (HK_nodup HK HKB _ _ _ _ HK0) as ND.
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (yfree_tail REST h mh lo B errv K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m CONT K0 TP CEIL LO SPB SPR) as TAIL.
  destruct HR as (HS & LR & BR & SR). destruct HS as ((pew & pad & HC & PEW) & H1 & H2 & H3 & H4).
  apply hand_cells_app in HC. destruct HC as [HH HA]. unfold hand_head_cells in HH.
  unfold alloc_cells in HA. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc] in HH, HA. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in HA.
  unfold yblocks in *.
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as HRG. unfold rblock_range, alloc_ceiling in HRG. cbn [blk_addr blk_size fst snd] in HRG.
  subst a0. unfold RY_FREE, RY_FREE_STACK, RY_LEX_FREE_STACK, RY_BUF_FREE_STACK, RY_WRAP_STACK, SIZEOF_HANDLE, alloc_ceiling, wz in *.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  assert (LR1 : forall m1, munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
                lexer_rep rsegs m1 (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72)).
  { intros m1 MU1 WM1. eapply (lexer_rep_transport_hi _ _ _ _ _ _ _ _ (mh_lid mh) LR MU1 WM1 RNG).
    - intros x Hx. right. apply in_or_app. left. apply in_or_app. left. exact Hx.
    - constructor; [| constructor]. cbn. unfold alloc_ceiling. lia. }
  assert (BR1 : forall m1, munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
                buf_rep rsegs m1 (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72)).
  { intros m1 MU1 WM1. eapply (buf_rep_transport_hi _ _ _ _ _ _ _ BR MU1 WM1 RNG).
    - intros x Hx. right. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hx.
    - constructor; [| constructor]. cbn. unfold alloc_ceiling. lia. }
  assert (PRES1 : forall m1, munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> ry_pres REST (bv_unsigned sp) [] m m1).
  { intros m1 MU1 WM1. eapply ryajl_pres_of_munch; [exact MU1| exact WM1|].
    intros a Ha Hc _. cbn. split; [| exact I].
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
    pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; right; exact Hb)) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia. }
  assert (OWN : forall m1, munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 -> wmono rsegs m m1 ->
            (HK s (((mh_id mh, mh_addr mh, 104) :: lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h) ++ buf_blocks (mh_decbuf mh) (h_decbuf h) ++ bs_blocks (mh_sid mh) (mh_stack mh) h) ++ REST) m1 mo
             /\ rauxv_ok m1 B) /\ ystatics m1).
  { intros m1 MU1 WM1. split.
    - eapply (yown_writes HK HKF); [exact HK0| exact AX| exact MU1| exact WM1| |].
      + constructor; [| constructor]. left. cbn. unfold alloc_ceiling. lia.
      + constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia.
    - eapply ystatics_munch; [exact YS| exact MU1| exact WM1|]. constructor; [cbn; unfold RY_CALLBACKS; lia| constructor]. }
  clear LR BR.
  unfold bs_blocks, bs_rep in *. destruct (h_stack_blk h) as [sb|] eqn:HSB.
  - (* [comment removed for export] *)
    destruct SR as [SBNZ _].
    pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; left; reflexivity)) as SRG.
    unfold rblock_range, alloc_ceiling in SRG. cbn [blk_addr blk_size fst snd] in SRG.
    rz_seg HKS HK0.
    step. carve_frame 16%nat STK. step. step.
    step. if_cases K1; zify_cond K1. 1:{ kill K1. }
    step. step.
    step. if_cases K2; zify_cond K2. 1:{ kill K2. }
    step. step. step. step.
    apply evt_done.
    destruct (OWN _ MU WM) as [[HK1 AX1] YS1]. pose proof (PRES1 _ MU WM) as PR1. specialize (LR1 _ MU WM). specialize (BR1 _ MU WM).
    lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI1; rename my into m1 end.
    lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into STK1 end.
    assert (HK1' : HK s ((mh_sid mh, mh_stack mh, h_stack_size h) :: ((mh_id mh, mh_addr mh, 104) :: lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h) ++ buf_blocks (mh_decbuf mh) (h_decbuf h)) ++ REST) m1 mo).
    { eapply HKP; [exact HK1| apply perm_yfree_bs]. }
    pose proof (HK_nodup HK HKB _ _ _ _ HK1') as ND1.
    clear MU WM HK1.
    eapply YWF with (p := mh_sid mh) (A := mh_stack mh) (n := h_stack_size h);
      [exact K0 | exact HK1' | left; reflexivity | exact AX1 | rewrite ESP; lia | rewrite ESP; exact STK1 | exact CEIL
      | rewrite ESP; unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR
      | exact MI1 | exact TP | reflexivity | ].
    cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' MI2 STK2 ERR2 AX2 HP HK2.
    replace (ret_pc (Z_to_bv 64 81160)) with (Z_to_bv 64 81160) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ESP in STK2, HP. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
    rewrite (lb_remove_head (mh_sid mh, mh_stack mh, h_stack_size h) _ ND1) in HP, HK2.
    eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 mo2 s2' errv pew pad);
      [ exact HK2 | eapply ystatics_pres; [exact YS1| exact HP] | eapply ypres_frame; [exact HP| eassumption| lia] | exact STK2 | exact MI2 | exact AX2 | exact ERR2
      | eapply ry_pres_trans; [exact PR1| apply ry_pres_of_rheap_pres; eapply rheap_pres_weaken; [exact HP| lia| intros b0 Hb0; right; apply in_or_app; right; exact Hb0]]
      | eapply ypres_block; [exact HP| eassumption| eexists; split; [left; reflexivity| cbn; lia]]
      | eapply ypres_block; [exact HP| eassumption| eexists; split; [left; reflexivity| cbn; lia]]
      | eapply (lexer_rep_pres_sub _ _ _ _ _ _ _ _ (mh_lid mh)); [exact LR1| exact HP| intros x Hx; right; apply in_or_app; left; apply in_or_app; left; exact Hx]
      | eapply buf_rep_pres_sub; [exact BR1| exact HP| intros x Hx; right; apply in_or_app; left; apply in_or_app; right; exact Hx] ].
  - (* [comment removed for export] *)
    rewrite app_nil_r in *.
    rz_seg HKS HK0.
    step. carve_frame 16%nat STK. step. step.
    step. if_cases K1; zify_cond K1. 1:{ kill K1. }
    step. step.
    step. if_cases K2; zify_cond K2. 2:{ rewrite SR in K2. kill K2. }
    apply evt_done.
    destruct (OWN _ MU WM) as [[HK1 AX1] YS1]. pose proof (PRES1 _ MU WM) as PR1. specialize (LR1 _ MU WM). specialize (BR1 _ MU WM).
    lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI1; rename my into m1 end.
    lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into STK1 end.
    eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mo s errv pew pad);
      [ exact HK1 | exact YS1 | eassumption | exact STK1 | exact MI1 | exact AX1 | exact ERR | exact PR1
      | eassumption | eassumption | exact LR1 | exact BR1 ].
Qed.
End S.
End RC__1.
