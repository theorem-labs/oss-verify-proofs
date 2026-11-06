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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Mem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlParser YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsParse.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma yleaf_yfree : forall p, yleaf (yfree p) tt.
Proof. intros p. unfold yfree. apply yl_free. apply yl_ret. Qed.
Lemma yleaf_ybuf_free : forall blk b, yleaf (ybuf_free blk b) tt.
Proof. intros blk b. unfold ybuf_free. destruct (yb_data b); [apply (yleaf_bind _ _ tt); apply yleaf_yfree| apply yleaf_yfree]. Qed.
Lemma yleaf_ylex_free : forall blk lx, yleaf (ylex_free blk lx) tt.
Proof. intros blk lx. unfold ylex_free. apply (yleaf_bind _ _ tt); [apply yleaf_ybuf_free| apply yleaf_yfree]. Qed.
Lemma yleaf_yajl_free : forall h, yleaf (yajl_free h) tt.
Proof.
  intros h. unfold yajl_free. apply (yleaf_bind _ _ tt).
  - destruct (h_stack_blk h); [apply yleaf_yfree| apply yl_ret].
  - apply (yleaf_bind _ _ tt); [apply yleaf_ybuf_free|]. apply (yleaf_bind _ _ tt); [apply yleaf_ylex_free| apply yleaf_yfree].
Qed.
Lemma yfuzz_leaf_some : forall txt h st h' cx', yleaf (yajl_alloc 1 1) (Some h) ->
  yleaf (ydo_parse jf_callbacks txt (zlength txt) h (mkCtx 0 0)) (st, h', cx') ->
  yleaf (yLLVMFuzzerTestOneInput txt (zlength txt)) 0.
Proof.
  intros txt h st h' cx' HL HP. unfold yLLVMFuzzerTestOneInput, yfuzz_one. apply (yleaf_bind _ _ (Some h)); [exact HL|]. cbv beta iota.
  apply (yleaf_bind _ _ (st, h', cx')); [exact HP|]. cbv beta iota.
  apply (yleaf_bind _ _ tt); [apply yl_ret|]. apply (yleaf_bind _ _ tt); [apply yleaf_yajl_free| apply yl_ret].
Qed.

Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YAL : yalloc_stmt HK.
Hypothesis YPA : yparse_stmt HK.
Hypothesis YFR : yfree_stmt HK.

(* [comment removed for export] *)
Ltac ybytes_eq := cbn; repeat (first [reflexivity | apply f_equal2; [apply Z_to_bv8_mod; vm_compute; reflexivity|]]).
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

Lemma yfuzz_spec : yfuzz_stmt HK.
Proof.
  unfold yfuzz_stmt. intros REST T txt lo B errv K. intros until s. intros K0 RY TXT TL TR YR FP A0 A1 CONT.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  pose proof TXT as TXT0. destruct TXT as (TB & TF & T0 & T62). pose proof (bytes_at_bound _ _ _ _ TB) as TBB. rewrite zbytes_length in TBB.
  pose proof (zlength_nonneg txt) as TL0.
  subst a0 a1. unfold RY_FUZZ, RY_FUZZ_STACK, RY_PARSE_STACK, RY_DO_PARSE_STACK, RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling, wz in *.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof TB as TB0. clear TB.
  rz_seg HKS HK0.
  step. carve_frame 48%nat STK. step. step. step. step.
  step. step. step. lit_store. step. step. step. step. lit_store.
  step. step. step. step. step. step.
  apply evt_done.
  (* [comment removed for export] *)
  destruct (proj1 (ycells_app rsegs _ _ [C8 (Z_to_bv 64 4294967297)] [C8 (Z_to_bv 64 0); C8 s2; C8 s1; C8 s0; C8 ra]) FR) as [CFGc FR']. clear FR.
  cbn [cells_size csize Nat.add] in FR'.
  destruct (proj1 (ycells_app rsegs _ _ [C8 (Z_to_bv 64 0)] [C8 s2; C8 s1; C8 s0; C8 ra]) FR') as [CTXc FRS]. clear FR'.
  cbn [cells_size csize Nat.add] in FRS.
  replace (bv_unsigned sp + -48 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -32) in FRS by lia.
  replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in CTXc by lia.
  lazymatch type of CFGc with rw_cells _ ?mx _ _ =>
    assert (CFG1 : rw_cells rsegs mx (bv_unsigned sp + -48) [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1)])
      by (eapply rw_cells_recast; [exact CFGc| cbn; repeat split; exact I| ybytes_eq| reflexivity]);
    assert (CTX1 : rw_cells rsegs mx (bv_unsigned sp + -40) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
      by (eapply rw_cells_recast; [exact CTXc| cbn; repeat split; exact I| reflexivity| reflexivity]) end.
  clear CFGc CTXc.
  (* [comment removed for export] *)
  assert (TXTP : forall SPx X ma mb, ry_pres REST SPx X ma mb -> (forall a, T <= a < T + zlength txt -> ~ yin_ivs X a) ->
            text_at rsegs ma T txt -> text_at rsegs mb T txt).
  { intros SPx X ma mb HP HX HT. eapply text_at_agree; [apply ry_pres_agree; exact HP| exact HT|].
    intros a Ha. split; [| apply HX; exact Ha]. destruct TR as [(bt & HBT & T1 & T2)|T00]; [| exfalso; lia].
    right; right. exists bt. split; [exact HBT| lia]. }
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK0 AX MU WM) as [HK1 AX1].
  { constructor; [| constructor]. left. cbn. unfold alloc_ceiling. lia. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
  pose proof (ystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS1.
  lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI1; rename my into m1 end.
  lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into STK1 end.
  lazymatch goal with H : rw_cells _ m1 216220 _ |- _ => rename H into ERR1 end.
  assert (PRES1 : ry_pres REST (bv_unsigned sp) [] m m1).
  { eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. cbn. split; [| exact I].
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
    pose proof (all_range_In _ _ RNG Hb) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia. }
  pose proof (TXTP _ _ _ _ PRES1 ltac:(intros a _ X; exact X) TXT0) as TXT1.
  clear MU WM AX HK0 YS TXT0.
  eapply (YAL REST (bv_unsigned sp + -48) (bv_unsigned sp + -40) lo B errv K);
    [ exact K0 | apply RYST_split; split; [exact HK1| exact YS1] | exact CFG1 | rewrite ESP; lia | lia
    | eapply yroom_le; [exact YR| lia]
    | split; [exact AX1|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK1|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_ALLOC_STACK, RY_LEX_ALLOC_STACK, RY_BUF_ALLOC_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR1|]; split; [exact MI1| exact TP]
    | reflexivity | reflexivity | reflexivity | reflexivity | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' h mh POST.
  destruct POST as ((MI2 & STK2 & (errv2 & ERR2) & AX2 & HP2) & CFG2 & RES).
  replace (ret_pc (Z_to_bv 64 80316)) with (Z_to_bv 64 80316) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK2, HP2. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
  pose proof (TXTP _ _ _ _ HP2 ltac:(intros a _ X; exact X) TXT1) as TXT2.
  apply ry_pres_nil in HP2.
  pose proof (ypres_frame _ _ _ _ _ _ HP2 FRS ltac:(lia)) as FRS2. clear FRS.
  pose proof (ypres_frame _ _ _ _ _ _ HP2 CTX1 ltac:(lia)) as CTX2. clear CTX1.
  assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
  { eapply ry_pres_trans; [exact PRES1|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP2| lia| auto]. }
  unfold wz in CFG2.
  clear HP2 MI1 STK1 ERR1 AX1 HK1 YS1 PRES1 TXT1 CFG1.
  (* [comment removed for export] *)
  destruct RES as (A0' & HNZ & MCX & HL & HR2 & RY2). subst a0'. unfold wz.
  pose proof (ypost_yleaf _ _ _ (yajl_alloc_post (zlength txt) TL0) HL) as AF. cbv beta iota in AF. destruct AF as (HINV & _).
  pose proof RY2 as RY2'. apply RYST_split in RY2'. destruct RY2' as [HK2 YS2].
  destruct (HK_blocks HK HKB _ _ _ _ HK2) as [RNG2 _].
  pose proof (all_range_In _ _ RNG2 (or_introl eq_refl)) as HRG. unfold rblock_range, alloc_ceiling, SIZEOF_HANDLE in HRG. cbn [blk_addr blk_size fst snd] in HRG.
  destruct HRG as (HRG0 & _ & _ & HRG3 & _).
  pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
  rz_seg HKS HK2.
  step. step. step. step.
  replace (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (zlength txt)) + 0))) with (Z_to_bv 64 (zlength txt)).
  2:{ rewrite unsigned_lit by lia. rewrite Z.add_0_r, ybv_swrap32_eq. rewrite Z.mod_small by lia. f_equal. lia. }
  apply evt_done. clear MU WM.
  eapply (YPA REST h mh (mkCtx 0 0) T txt lo B errv2 K);
    [ exact K0 | exact RY2 | exact HR2
    | rewrite MCX; split; [unfold ctx_cells; cbn [cx_arrayLevel cx_objectLevel]; unfold wz; exact CTX2| cbn; lia]
    | exact TXT2 | exact TL | exact TR | exact HINV
    | rewrite MCX, ESP; lia | rewrite MCX; lia
    | exact YR
    | split; [exact AX2|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK2|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_DO_PARSE_STACK, RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR2|]; split; [exact MI2| exact TP]
    | reflexivity | reflexivity | reflexivity | ].
  cbv beta. intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x m3 mo3 s3' F' st h' cx' mh' LK POST FS.
  destruct POST as ((MI3 & STK3 & (errv3 & ERR3) & AX3 & HP3) & HPL & A0' & HR3 & MHS & CTX3 & TXT3 & LK0 & RY3). subst a0x.
  replace (ret_pc (Z_to_bv 64 80332)) with (Z_to_bv 64 80332) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK3, HP3. rewrite (ry_errno_lit tp TP) in ERR3. unfold RERRNO in ERR3. rewrite MCX in HP3, CTX3. unfold mh_same in MHS. destruct MHS as (MID & MADDR & MREST).
  assert (FRS3 : rw_cells rsegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree; [apply ry_pres_agree; exact HP3| exact FRS2|]. cbn [cells_size csize Nat.add]. intros a Ha. split; [left; lia|]. cbn. lia. }
  assert (CFG3 : rw_cells rsegs m3 (bv_unsigned sp + -48) [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1)]).
  { eapply rw_cells_agree; [apply ry_pres_agree; exact HP3| exact CFG2|]. cbn [cells_size csize Nat.add]. intros a Ha. split; [left; lia|]. cbn. lia. }
  assert (PRES3 : ry_pres REST (bv_unsigned sp) [] m m3).
  { eapply ry_pres_trans; [exact PRES2|]. intros a Ha Hc _. apply HP3; [exact Ha| |].
    - destruct Hc as [Hc|[Hc|Hb]]; [left; lia| right; left; exact Hc| right; right; exact Hb].
    - cbn. intros [X|[]]. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (all_range_In _ _ RNG Hb) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia. }
  pose proof RY3 as RY3'. apply RYST_split in RY3'. destruct RY3' as [HK3 YS3].
  destruct CTX3 as [CTXc3 _]. unfold ctx_cells in CTXc3.
  clear HP3 MI2 STK2 ERR2 AX2 HK2 YS2 RY2 PRES2 FRS2 CFG2 CTX2 TXT2.
  pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
  rz_seg HKS HK3.
  step. step.
  apply evt_done. clear MU WM.
  eapply (YFR (LK ++ REST) h' mh' lo B errv3 K);
    [ exact K0 | exact RY3 | exact HR3
    | split; [exact AX3|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK3|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_FREE_STACK, RY_LEX_FREE_STACK, RY_BUF_FREE_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR3|]; split; [exact MI3| exact TP]
    | rewrite MADDR; reflexivity | ].
  cbv beta. intros t0y t1y t2y a0y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y m4 mo4 s4' POST.
  destruct POST as ((MI4 & STK4 & (errv4 & ERR4) & AX4 & HP4) & RY4).
  replace (ret_pc (Z_to_bv 64 80340)) with (Z_to_bv 64 80340) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK4, HP4. rewrite (ry_errno_lit tp TP) in ERR4. unfold RERRNO in ERR4.
  pose proof (TXTP _ _ _ _ (ry_pres_weaken (LK ++ REST) REST (bv_unsigned sp + -48) (bv_unsigned sp + -48) [] [] _ _ HP4 ltac:(clear; lia) ltac:(intros b0 Hb0; apply in_or_app; right; exact Hb0) ltac:(intros a X; exact X))
                ltac:(intros a _ X; exact X) TXT3) as TXT4.
  apply ry_pres_nil in HP4. apply RYST_split in RY4. destruct RY4 as [HK4 YS4].
  pose proof (ypres_frame _ _ _ _ _ _ HP4 FRS3 ltac:(lia)) as FRS4.
  pose proof (ypres_frame _ _ _ _ _ _ HP4 CFG3 ltac:(lia)) as CFG4.
  pose proof (ypres_frame _ _ _ _ _ _ HP4 CTXc3 ltac:(lia)) as CTX4.
  assert (PRES4 : ry_pres REST (bv_unsigned sp) [] m m4).
  { eapply ry_pres_trans; [exact PRES3|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP4| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0]. }
  clear HP4 FRS3 CFG3 CTXc3 TXT3 MI3 STK3 ERR3 AX3 HK3 YS3 RY3 PRES3.
  pose proof (munch_refl ([] : list (Z * Z)) m4) as MU. pose proof (wmono_refl rsegs m4) as WM.
  rz_seg HKS HK4.
  step. step. step. step. step. step. step.
  apply evt_done.
  lazymatch goal with H1 : rw_cells _ ?mx (bv_unsigned sp + -48) _, H2 : rw_cells _ _ (bv_unsigned sp + -40) _, H3 : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ =>
    assert (FR : rw_cells rsegs mx (bv_unsigned sp + -48) [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 (cx_arrayLevel cx')); C4 (Z_to_bv 64 (cx_objectLevel cx')); C8 s2; C8 s1; C8 s0; C8 ra]);
    [ apply (proj2 (ycells_app rsegs _ _ [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1)] _)); split; [exact H1|]; cbn [cells_size csize Nat.add];
      replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) by lia;
      apply (proj2 (ycells_app rsegs _ _ [C4 (Z_to_bv 64 (cx_arrayLevel cx')); C4 (Z_to_bv 64 (cx_objectLevel cx'))] _)); split; [exact H2|]; cbn [cells_size csize Nat.add];
      replace (bv_unsigned sp + -40 + Z.of_nat 8) with (bv_unsigned sp + -32) by lia; exact H3
    | clear H1 H2 H3 ] end.
  lazymatch goal with H : stk _ _ lo _ |- _ => rename H into STKf end.
  release_frame FR STKf (bv_unsigned sp).
  eapply CONT with (LK := LK); [| exact FS]. unfold yfuzz_rpost.
  split; [| split; [reflexivity| split; [exact TXT4| split; [eapply yfuzz_leaf_some; [exact HL| exact HPL]| split; [exact LK0| apply RYST_split; split; [exact HK4| exact YS4]]]]]].
  split; [exact MI4|]. split; [exact STKf|]. split; [exists errv4; rewrite (ry_errno_lit tp TP); assumption|]. split; [exact AX4| exact PRES4].
Qed.
End S.
End RC__1.
