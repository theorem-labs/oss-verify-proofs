(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UF_memset.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma yleaf_ymalloc : forall n r, yleaf (ymalloc n) r.
Proof. intros n r. unfold ymalloc. apply (yl_malloc _ _ r). apply yl_ret. Qed.
Lemma yleaf_yfree : forall p, yleaf (yfree p) tt.
Proof. intros p. unfold yfree. apply yl_free. apply yl_ret. Qed.

(* [comment removed for export] *)
Lemma all_range_bufdata : forall pre mb b post,
  all_range (pre ++ buf_blocks mb b ++ post) -> yb_data b <> None ->
  0 < mb_data mb /\ mb_data mb + yb_len b <= alloc_ceiling /\ (mb_data mb + yb_len b <= 0x10000 \/ 0x57000 <= mb_data mb).
Proof.
  intros pre mb b post RNG HD.
  assert (HI : In (mb_did mb, mb_data mb, yb_len b) (pre ++ buf_blocks mb b ++ post)).
  { apply in_or_app. right. apply in_or_app. left. unfold buf_blocks. destruct (yb_data b); [| congruence]. right. left. reflexivity. }
  pose proof (all_range_In _ _ RNG HI) as X. unfold rblock_range in X. cbn [blk_addr blk_size fst snd] in X. tauto.
Qed.

Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YWM : ywrap_malloc_stmt HK.
Hypothesis YWF : ywrap_free_stmt HK.
Hypothesis YBA : ybuf_alloc_stmt HK.
Hypothesis YBF : ybuf_free_stmt HK.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).
Lemma land7_of_mod8 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.
Lemma mod8_of_mod16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. rewrite <- (Z.mod_mod_divide x 16 8) by (try lia; exists 2; reflexivity). rewrite H. reflexivity. Qed.
Lemma land7_of_mod16 : forall x, x mod 16 = 0 -> Z.land x 7 = 0.
Proof. intros x H. apply land7_of_mod8, mod8_of_mod16, H. Qed.

(* [comment removed for export] *)
Lemma ylex_alloc_spec : ylex_alloc_stmt HK.
Proof.
  unfold ylex_alloc_stmt. intros REST AF aC v8 lo B errv K. intros until s. intros K0 [AFP AFA] RY YAF AFIN HAC HV8 YR FP A0 A1 A2 CONT. pose proof (land7_of_mod8 _ AFA) as L7A.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  pose proof (rw_cells_bound _ _ _ _ YAF) as YAFB. cbn [cells_size csize Nat.add alloc_cells length] in YAFB.
  destruct AFIN as (hb & HBIN & HB1 & HB2).
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  pose proof (all_range_In _ _ RNG HBIN) as HBR. unfold rblock_range in HBR.
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  subst a0 a1 a2. unfold RY_LEX_ALLOC, RY_LEX_ALLOC_STACK, RY_BUF_ALLOC_STACK, RY_WRAP_STACK, alloc_ceiling, wz in *.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in YAF.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  step. carve_frame 48%nat STK. step. step. step. step. step.
  step. if_cases G0; zify_cond G0. 1:{ kill G0. }
  step. zstep. step. if_cases G1; zify_cond G1. 1:{ kill G1. }
  step. step. step. step. step. step.
  apply evt_done.
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK0 AX MU WM) as [HK1 AX1].
  { constructor; [| constructor]. left. cbn. unfold alloc_ceiling. lia. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
  eapply YWM; [exact K0 | exact HK1 | exact AX1 | rewrite ESP; lia | rewrite ESP; exact STK | exact CEIL
               | rewrite ESP; unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR
               | exact MI | exact TP | reflexivity | unfold NUSERc; lia | eapply yroom_lt; [exact YR| lia] | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' errv2 p L MI2 STK2 ERR2 AX2 HP A0' BR HK2 NEW.
  replace (ret_pc (Z_to_bv 64 81692)) with (Z_to_bv 64 81692) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK2, HP. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
  pose proof (ystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS1.
  pose proof (ystatics_pres _ _ _ _ YS1 HP) as YS2. clear YS YS1.
  pose proof (ypres_frame _ _ _ _ _ _ HP FR ltac:(lia)) as FR2. clear FR.
  pose proof (ypres_block _ _ _ _ _ _ HP YAF ltac:(exists hb; split; [exact HBIN| cbn; lia])) as YAF2. clear YAF.
  assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
  { eapply ry_pres_trans.
    - eapply ryajl_pres_of_munch; [exact MU| exact WM|].
      intros a Ha Hc _. cbn. split; [| exact I].
      destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (all_range_In _ _ RNG Hb) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia.
    - eapply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
  clear MU WM MI HK1 AX1 AX ERR STK HP m0.
  (* [comment removed for export] *)
  subst a0'. unfold rblock_range, alloc_ceiling in BR. unfold wz. destruct NEW as [junk2 NEW].
  destruct (HK_blocks HK HKB _ _ _ _ HK2) as [RNG2 SEP2]. cbn [all_sep] in SEP2. destruct SEP2 as [SEPL _].
  pose proof (sep_from_In _ _ _ SEPL HBIN) as SEPhb. unfold bsep in SEPhb. cbn [blk_addr blk_size fst snd] in SEPhb.
  assert (UL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (U48 : bv_unsigned (Z_to_bv 64 48) = 48) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(L, L + 48)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
  rz_seg HKS HK2.
  step. step. if_cases K1; zify_cond K1. 1:{ kill K1. }
  step. step. step. step.
  call memset_spec.
  1:{ rewrite UL, U48. exact NEW. }
  1:{ assumption. }
  lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 L)) _ |- _ => rename H into Z48; rewrite UL, U48 in Z48 end.
  change (Z.to_nat 48) with 48%nat in Z48.
  replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in Z48 by reflexivity.
  step. step.
  apply evt_done.
  (* [comment removed for export] *)
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK2 AX2 MU WM) as [HK3 AX3].
  { constructor; [| constructor]. right; right. exists (p, L, 48). split; [left; reflexivity| cbn; lia]. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
  pose proof (ystatics_munch _ _ _ YS2 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS3.
  lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI3; rename my into m3 end.
  assert (PRES3 : ry_pres REST (bv_unsigned sp) [] m m3).
  { eapply ry_pres_trans; [exact PRES2|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. cbn. split; [| exact I].
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
    pose proof (sep_from_In _ _ _ SEPL Hb) as Hs. unfold bsep in Hs. cbn [blk_addr blk_size fst snd] in Hs. lia. }
  clear MU WM YS2 PRES2 AX2.
  eapply (YBA ((p, L, 48) :: REST) AF lo B errv2 K);
    [ exact K0 | split; [exact AFP| exact AFA] | apply RYST_split; split; [exact HK3| exact YS3] | exact YAF2
    | exists hb; split; [right; exact HBIN| cbn; lia]
    | apply yroom_cons; exact YR
    | split; [exact AX3|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK2|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_BUF_ALLOC_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR2|]; split; [exact MI3| exact TP]
    | reflexivity | ].
  cbv beta. intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m4 mo4 s4' pb B0 POST.
  destruct POST as ((MI4 & STK4 & (errv4 & ERR4) & AX4 & HP4) & YAF4 & A0'' & B0NZ & BS4 & RY4).
  replace (ret_pc (Z_to_bv 64 81724)) with (Z_to_bv 64 81724) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK4, HP4. rewrite (ry_errno_lit tp TP) in ERR4. unfold RERRNO in ERR4.
  apply ry_pres_nil in HP4.
  pose proof (ystatics_pres _ _ _ _ YS3 HP4) as YS4.
  pose proof (ypres_frame _ _ _ _ _ _ HP4 FR2 ltac:(lia)) as FR4. clear FR2.
  pose proof (ypres_block _ _ _ _ _ _ HP4 Z48 ltac:(eexists; split; [left; reflexivity| cbn; lia])) as Z48'. clear Z48.
  assert (PRES4 : ry_pres REST (bv_unsigned sp) [] m m4).
  { eapply ry_pres_trans; [exact PRES3|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP4| lia| intros b0 Hb0; right; exact Hb0]. }
  unfold alloc_cells in YAF4. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF4. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in YAF4.
  clear HP4 YS3 PRES3 MI3 STK2 ERR2 AX3 HK3 YAF2.
  (* [comment removed for export] *)
  subst a0''. unfold wz. apply RYST_split in RY4. destruct RY4 as [HK4 _].
  destruct BS4 as (BC4 & DZ4 & RL4 & RU4). unfold buf_cells, ybuf_zero in BC4. cbn [buf_state_code yb_state yb_len yb_used] in BC4. unfold wz in BC4.
  pose proof (rw_cells_bound _ _ _ _ BC4) as BCB. cbn [cells_size csize Nat.add length] in BCB.
  destruct (HK_blocks HK HKB _ _ _ _ HK4) as [RNG4 SEP4].
  pose proof (all_range_In _ _ RNG4 (or_introl eq_refl)) as BBR. unfold rblock_range, alloc_ceiling in BBR. cbn [blk_addr blk_size fst snd] in BBR.
  cbn [all_sep sep_from] in SEP4. destruct SEP4 as ((SBL & SBR) & _). unfold bsep in SBL. cbn [blk_addr blk_size fst snd] in SBL.
  assert (UB0 : bv_unsigned (Z_to_bv 64 B0) = B0) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(L, L + 48)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
  unfold SIZEOF_BUF in *.
  pose proof (land7_of_mod16 _ (proj1 (proj2 BR))) as L7L.
  rz_seg HKS HK4.
  zstep. step. if_cases G2; zify_cond G2. 1:{ kill G2. }
  step. step. step. step. step.
  step. step. step. step. step. step. step.
  apply evt_done.
  lazymatch goal with H : stk _ _ lo _ |- _ => rename H into STK5 end.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => rename H into FR5 end.
  release_frame FR5 STK5 (bv_unsigned sp).
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into mf end.
  lazymatch goal with H : rw_cells _ mf L _ |- _ => rename H into LXf end.
  lazymatch goal with H : rw_cells _ mf B0 _ |- _ => rename H into BCf end.
  lazymatch goal with H : rw_cells _ mf AF _ |- _ => rename H into YAFf end.
  lazymatch goal with H : rw_cells _ mf 218620 _ |- _ => rename H into ERRf end.
  lazymatch goal with H : mem_inv _ mf |- _ => rename H into MIf end.
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK4 AX4 MU WM) as [HKf AXf].
  { constructor; [| constructor]. right; right. exists (p, L, 48). split; [right; left; reflexivity| cbn; lia]. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
  pose proof (ystatics_munch _ _ _ YS4 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YSf.
  assert (PRESf : ry_pres REST (bv_unsigned sp) [] m mf).
  { eapply ry_pres_trans; [exact PRES4|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. cbn. split; [| exact I].
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
    pose proof (sep_from_In _ _ _ SEPL Hb) as Hs. unfold bsep in Hs. cbn [blk_addr blk_size fst snd] in Hs. lia. }
  assert (HKf' : HK s4' ((p, L, 48) :: (pb, B0, 32) :: REST) mf mo4) by (eapply HKP; [exact HKf| apply Permutation.perm_swap]).
  eapply CONT with (L := L) (lid := p) (mbl := mkMB pb B0 pb 0) (lx := mkLexer 0 0 LE_ok ybuf_zero 0%nat 0 0 aC v8).
  unfold ylex_alloc_rpost.
  split; [| split; [exact YAFf| split; [reflexivity| split; [lia| split; [| split; [| split; [reflexivity| apply RYST_split; split; [exact HKf'| exact YSf]]]]]]]].
  * split; [exact MIf|]. split; [exact STK5|]. split; [eexists; rewrite (ry_errno_lit tp TP); exact ERRf|]. split; [exact AXf| exact PRESf].
  * exists 0%nat. unfold ylex_alloc. apply (yleaf_bind _ _ (Some 0%nat)); [apply yleaf_ymalloc|]. cbn beta iota.
    apply (yleaf_bind _ _ (Some 0%nat)); [unfold ybuf_alloc; apply yleaf_ymalloc|]. apply yl_ret.
  * split.
    -- split; [| cbn; lia]. unfold lexer_cells. cbn [lx_lineOff lx_charOff lx_error lex_error_code lx_bufOff lx_bufInUse lx_allowComments lx_validateUTF8 mb_addr]. unfold wz.
       eapply rw_cells_recast; [exact LXf| cbn; repeat split; reflexivity| reflexivity| reflexivity].
    -- split; [| split; [cbn; exact I| cbn; constructor]].
       split; [unfold buf_cells, ybuf_zero; cbn [buf_state_code yb_state yb_len yb_used mb_addr mb_data]; unfold wz; exact BCf| split; [cbn; tauto| cbn; lia]].
Qed.

(* [comment removed for export] *)
Lemma ylex_free_spec : ylex_free_stmt HK.
Proof.
  unfold ylex_free_stmt. intros REST lid L AF mbl lx lo B errv K. intros until s. intros K0 (LP & LA & AFP & AFA & MBP & MBA) RY LR YAF AFIN FP A0 CONT. pose proof (land7_of_mod8 _ LA) as L7L. pose proof (land7_of_mod8 _ AFA) as L7A.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  pose proof (rw_cells_bound _ _ _ _ YAF) as YAFB. cbn [cells_size csize Nat.add alloc_cells length] in YAFB.
  destruct AFIN as (hb & HBIN & HB1 & HB2).
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP]. pose proof (HK_nodup HK HKB _ _ _ _ HK0) as ND.
  unfold lexer_blocks in *. cbn [app] in HK0, RNG, SEP, ND.
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as LRG. unfold rblock_range, alloc_ceiling in LRG. cbn [blk_addr blk_size fst snd] in LRG.
  assert (HBIN' : In hb ((lid, L, SIZEOF_LEXER) :: buf_blocks mbl (lx_buf lx) ++ REST)) by (right; apply in_or_app; right; exact HBIN).
  pose proof (all_range_In _ _ RNG HBIN') as HBR. unfold rblock_range, alloc_ceiling in HBR.
  cbn [all_sep] in SEP. destruct SEP as [SEPL _].
  pose proof (sep_from_In _ _ _ SEPL ltac:(apply in_or_app; right; exact HBIN)) as SEPhb. unfold bsep in SEPhb. cbn [blk_addr blk_size fst snd] in SEPhb.
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct LR as ((LC & L1 & L2 & L3 & L4 & L5 & L6) & BR). unfold lexer_cells in LC.
  pose proof (rw_cells_bound _ _ _ _ LC) as LCB. cbn [cells_size csize Nat.add length] in LCB.
  pose proof BR as BR'. destruct BR' as ((BC & _ & _ & _) & _ & _). pose proof (rw_cells_bound _ _ _ _ BC) as BCB. rewrite buf_cells_size in BCB. clear BC.
  subst a0. unfold RY_LEX_FREE, RY_LEX_FREE_STACK, RY_BUF_FREE_STACK, RY_WRAP_STACK, SIZEOF_LEXER, SIZEOF_BUF, alloc_ceiling, wz in *.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in YAF.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  step. carve_frame 16%nat STK. step. step.
  step. if_cases G0; zify_cond G0. 1:{ kill G0. }
  step. zstep. step. if_cases G1; zify_cond G1. 1:{ kill G1. }
  step. step.
  apply evt_done.
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK0 AX MU WM) as [HK1 AX1].
  { constructor; [| constructor]. left. cbn. unfold alloc_ceiling. lia. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
  pose proof (ystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS1.
  lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI1; rename my into m1 end.
  lazymatch goal with H : rw_cells _ m1 L _ |- _ => rename H into LC1 end.
  lazymatch goal with H : rw_cells _ m1 AF _ |- _ => rename H into YAF1 end.
  lazymatch goal with H : rw_cells _ m1 218620 _ |- _ => rename H into ERR1 end.
  lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into STK1 end.
  assert (PRES1 : ry_pres REST (bv_unsigned sp) [] m m1).
  { eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. cbn. split; [| exact I].
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
    pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; right; exact Hb)) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia. }
  pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; left; reflexivity)) as BRG. unfold rblock_range, alloc_ceiling in BRG. cbn [blk_addr blk_size fst snd] in BRG.
  assert (BR1 : buf_rep usegs m1 mbl (lx_buf lx) AF).
  { eapply buf_rep_transport; [exact BR| exact MU| exact WM| cbv [disjoint_from fst snd]; lia|].
    intros HD. destruct (all_range_bufdata [(lid, L, 48)] mbl (lx_buf lx) REST RNG HD) as (_ & X & _). unfold alloc_ceiling in X. cbv [disjoint_from fst snd]. lia. }
  assert (HK1' : HK s (buf_blocks mbl (lx_buf lx) ++ (lid, L, 48) :: REST) m1 mo) by (eapply HKP; [exact HK1| apply Permutation.Permutation_middle]).
  clear MU WM.
  eapply (YBF ((lid, L, 48) :: REST) mbl (lx_buf lx) AF lo B errv K);
    [ exact K0 | split; [exact MBP | split; [exact MBA | split; [exact AFP | exact AFA]]] | apply RYST_split; split; [exact HK1'| exact YS1] | exact BR1 | exact YAF1
    | exists hb; split; [right; exact HBIN| cbn; lia]
    | split; [exact AX1|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK1|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_BUF_FREE_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR1|]; split; [exact MI1| exact TP]
    | reflexivity | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' POST.
  destruct POST as ((MI2 & STK2 & (errv2 & ERR2) & AX2 & HP2) & YAF2 & RY2).
  replace (ret_pc (Z_to_bv 64 81892)) with (Z_to_bv 64 81892) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK2, HP2. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
  apply ry_pres_nil in HP2. apply RYST_split in RY2. destruct RY2 as [HK2 YS2].
  pose proof (ypres_frame _ _ _ _ _ _ HP2 FR ltac:(lia)) as FR2. clear FR.
  pose proof (ypres_block _ _ _ _ _ _ HP2 LC1 ltac:(eexists; split; [left; reflexivity| cbn; lia])) as LC2. clear LC1.
  assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
  { eapply ry_pres_trans; [exact PRES1|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP2| lia| intros b0 Hb0; right; exact Hb0]. }
  unfold alloc_cells in YAF2. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF2. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in YAF2.
  clear HP2 MI1 STK1 ERR1 AX1 HK1 HK1' YAF1 YS1 BR1.
  pose proof (HK_nodup HK HKB _ _ _ _ HK2) as ND2.
  (* [comment removed for export] *)
  pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
  rz_seg HKS HK2.
  step. step. if_cases Ga; zify_cond Ga. 1:{ kill Ga. }
  zstep. step. if_cases Gb; zify_cond Gb. 1:{ kill Gb. }
  step. step. step. step. step. step. step.
  apply evt_done. release_frame FR2 STK2 (bv_unsigned sp).
  eapply YWF with (p := lid) (A := L) (n := 48);
    [exact K0 | exact HK2 | left; reflexivity | exact AX2 | lia | exact STK2 | exact CEIL
    | unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR2
    | exact MI2 | exact TP | reflexivity | ].
  cbv beta. intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x m3 mo3 s3' MI3 STK3 ERR3 AX3 HP3 HK3.
  rewrite (lb_remove_head (lid, L, 48) REST ND2) in HP3, HK3.
  eapply CONT. unfold ylex_free_rpost.
  split; [| split; [eapply ypres_block; [exact HP3| exact YAF2| exists hb; split; [exact HBIN| cbn; lia]]
                  | apply RYST_split; split; [exact HK3| eapply ystatics_pres; [exact YS2| exact HP3]]]].
  split; [exact MI3|]. split; [exact STK3|]. split; [eexists; exact ERR3|]. split; [exact AX3|].
  eapply ry_pres_trans; [exact PRES2|]. apply ry_pres_of_rheap_pres. exact HP3.
Qed.
End S.

End RC__1.
