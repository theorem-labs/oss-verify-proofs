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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RF_memset.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLeaf YajlFactsBuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YWM : ywrap_malloc_stmt HK.
Hypothesis YWF : ywrap_free_stmt HK.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

Lemma ybuf_alloc_spec : ybuf_alloc_stmt HK.
Proof.
  unfold ybuf_alloc_stmt. intros REST AF lo B errv K. intros until s. intros K0 RY YAF AFIN YR FP A0 CONT.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  pose proof (rw_cells_bound _ _ _ _ YAF) as YAFB. cbn [cells_size csize Nat.add alloc_cells length] in YAFB.
  destruct AFIN as (hb & HBIN & HB1 & HB2).
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  pose proof (all_range_In _ _ RNG HBIN) as HBR. unfold rblock_range in HBR.
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  subst a0. unfold RY_BUF_ALLOC, RY_BUF_ALLOC_STACK, RY_WRAP_STACK, alloc_ceiling, wz in *.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in YAF.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  rz_seg HKS HK0.
  step. carve_frame 32%nat STK. step. step. step. step. step. step. step. step.
  apply evt_done.
  (* [comment removed for export] *)
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK0 AX MU WM) as [HK1 AX1].
  { constructor; [| constructor]. left. cbn. unfold alloc_ceiling. lia. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
  eapply YWM; [exact K0 | exact HK1 | exact AX1 | rewrite ESP; lia | rewrite ESP; exact STK | exact CEIL
               | rewrite ESP; unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR
               | exact MI | exact TP | reflexivity | unfold NUSERc; lia | eapply yroom_lt; [exact YR| lia] | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' errv2 p B0 MI2 STK2 ERR2 AX2 HP A0' BR HK2 NEW.
  replace (ret_pc (Z_to_bv 64 86004)) with (Z_to_bv 64 86004) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK2, HP. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
  (* [comment removed for export] *)
  pose proof (ystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS1.
  pose proof (ystatics_pres _ _ _ _ YS1 HP) as YS2. clear YS YS1.
  pose proof (ypres_frame _ _ _ _ _ _ HP FR ltac:(lia)) as FR2. clear FR.
  pose proof (ypres_block _ _ _ _ _ _ HP YAF ltac:(exists hb; split; [exact HBIN| cbn; lia])) as YAF2. clear YAF.
  (* [comment removed for export] *)
  assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
  { eapply ry_pres_trans.
    - eapply ryajl_pres_of_munch; [exact MU| exact WM|].
      intros a Ha Hc _. cbn. split; [| exact I].
      destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (all_range_In _ _ RNG Hb) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia.
    - eapply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
  clear MU WM MI HK1 AX1 AX ERR STK HP m0.
  (* [comment removed for export] *)
  - subst a0'. unfold rblock_range, alloc_ceiling in BR. unfold wz. destruct NEW as [junk2 NEW].
    destruct (HK_blocks HK HKB _ _ _ _ HK2) as [RNG2 SEP2]. cbn [all_sep] in SEP2. destruct SEP2 as [SEPB _].
    pose proof (sep_from_In _ _ _ SEPB HBIN) as SEPhb. unfold bsep in SEPhb. cbn [blk_addr blk_size fst snd] in SEPhb.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB rsegs m2 B0 [] 32 junk2 [] [24%nat; 8%nat] NEW eq_refl) as NEW'. clear NEW.
    cbn [app mk_CB_cells] in NEW'.
    destruct (proj1 (ycells_app rsegs m2 B0 [CB 24 (take 24 junk2)] [CB 8 (take 8 (drop 24 junk2))]) NEW') as [D24 D8]. clear NEW'.
    cbn [cells_size csize Nat.add] in D8. change (Z.of_nat 24) with 24 in D8.
    assert (UB0 : bv_unsigned (Z_to_bv 64 B0) = B0) by (apply unsigned_lit; lia).
    assert (U24 : bv_unsigned (Z_to_bv 64 24) = 24) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(B0, B0 + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    rz_seg HKS HK2.
    step. if_cases K1; zify_cond K1. 1:{ kill K1. }
    step. step. step. step.
    call memset_spec.
    1:{ rewrite UB0, U24. exact D24. }
    1:{ assumption. }
    lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 B0)) _ |- _ => rename H into Z24; rewrite UB0, U24 in Z24 end.
    change (Z.to_nat 24) with 24%nat in Z24.
    replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in Z24 by reflexivity.
    step. step. step. step. step. step. step. step.
    apply evt_done.
    lazymatch goal with H : stk _ _ lo _ |- _ => rename H into STK3 end.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => rename H into FR3 end.
    release_frame FR3 STK3 (bv_unsigned sp).
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into mf end.
    lazymatch goal with H : rw_cells _ mf (B0 + 24) _ |- _ => rename H into D8f end.
    lazymatch goal with H : rw_cells _ mf B0 _ |- _ => rename H into Z24f end.
    lazymatch goal with H : rw_cells _ mf AF _ |- _ => rename H into YAFf end.
    lazymatch goal with H : rw_cells _ mf 216220 _ |- _ => rename H into ERRf end.
    lazymatch goal with H : mem_inv _ mf |- _ => rename H into MIf end.
    (* [comment removed for export] *)
    destruct (yown_writes HK HKF _ _ _ _ _ _ B HK2 AX2 MU WM) as [HKf AXf].
    { constructor; [| constructor]. right; right. exists (p, B0, 32). split; [left; reflexivity| cbn; lia]. }
    { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    pose proof (ystatics_munch _ _ _ YS2 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YSf.
    (* [comment removed for export] *)
    assert (PRESf : ry_pres REST (bv_unsigned sp) [] m mf).
    { eapply ry_pres_trans; [exact PRES2|].
      eapply ryajl_pres_of_munch; [exact MU| exact WM|].
      intros a Ha Hc _. cbn. split; [| exact I].
      destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (sep_from_In _ _ _ SEPB Hb) as Hs. unfold bsep in Hs. cbn [blk_addr blk_size fst snd] in Hs. lia. }
    (* [comment removed for export] *)
    pose proof (proj2 (ycells_app rsegs mf B0 [CB 24 (repeat (Z_to_bv 8 0) 24)] [C8 (Z_to_bv 64 AF)]) (conj Z24f D8f)) as BC.
    cbn [app] in BC.
    eapply CONT with (p := p) (B0 := B0). unfold ybuf_alloc_rpost.
    split; [| split; [exact YAFf| split; [reflexivity| split; [lia| split; [| apply RYST_split; split; [exact HKf| exact YSf]]]]]].
    + split; [exact MIf|]. split; [exact STK3|]. split; [eexists; rewrite (ry_errno_lit tp TP); exact ERRf|].
      split; [exact AXf| exact PRESf].
    + split; [| split; [cbn; tauto| cbn; lia]].
      eapply rw_cells_recast; [exact BC| cbn; repeat split; exact I| reflexivity| reflexivity].
Qed.
(* [comment removed for export] *)
Lemma ybuf_free_spec : ybuf_free_stmt HK.
Proof.
  unfold ybuf_free_stmt. intros REST mb b AF lo B errv K. intros until s. intros K0 RY BR YAF AFIN FP A0 CONT.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  pose proof (rw_cells_bound _ _ _ _ YAF) as YAFB. cbn [cells_size csize Nat.add alloc_cells length] in YAFB.
  destruct AFIN as (hb & HBIN & HB1 & HB2).
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP]. pose proof (HK_nodup HK HKB _ _ _ _ HK0) as ND.
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as BRNG. unfold rblock_range, alloc_ceiling in BRNG. cbn [blk_addr blk_size fst snd] in BRNG.
  assert (HBIN' : In hb (buf_blocks mb b ++ REST)) by (apply in_or_app; right; exact HBIN).
  pose proof (all_range_In _ _ RNG HBIN') as HBR. unfold rblock_range, alloc_ceiling in HBR.
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct BR as ((BC & DZ & RL & RU) & BD & FB). unfold buf_cells in BC.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. cbn [cells_size csize Nat.add] in BCB.
  subst a0. unfold RY_BUF_FREE, RY_BUF_FREE_STACK, RY_WRAP_STACK, alloc_ceiling, wz in *.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in YAF.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (yb_data b) as [dp|] eqn:HD.
  - (* [comment removed for export] *)
    assert (D0 : mb_data mb <> 0) by (intros E; apply DZ in E; congruence).
    unfold buf_blocks in *. rewrite HD in *.
    cbn [all_sep sep_from app] in SEP. destruct SEP as ((SBD & SBR) & SDR & _). unfold bsep in SBD. cbn [blk_addr blk_size fst snd] in SBD.
    pose proof (all_range_In _ _ RNG (or_intror (or_introl eq_refl))) as DRNG. unfold rblock_range, alloc_ceiling in DRNG. cbn [blk_addr blk_size fst snd] in DRNG.
    clear BD.
    rz_seg HKS HK0.
    step. carve_frame 16%nat STK. step. step.
    step. if_cases K1; zify_cond K1. 1:{ kill K1. }
    step. step.
    step. if_cases K2; zify_cond K2. 1:{ kill K2. }
    step. step. step. step.
    apply evt_done.
    (* [comment removed for export] *)
    destruct (yown_writes HK HKF _ _ _ _ _ _ B HK0 AX MU WM) as [HK1 AX1].
    { constructor; [| constructor]. left. cbn. unfold alloc_ceiling. lia. }
    { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    eapply YWF with (p := mb_did mb) (A := mb_data mb) (n := yb_len b);
      [exact K0 | exact HK1 | right; left; reflexivity | exact AX1 | rewrite ESP; lia | rewrite ESP; exact STK | exact CEIL
      | rewrite ESP; unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR
      | exact MI | exact TP | reflexivity | ].
    cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' MI2 STK2 ERR2 AX2 HP HK2.
    replace (ret_pc (Z_to_bv 64 86108)) with (Z_to_bv 64 86108) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ESP in STK2, HP. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
    rewrite (lb_remove_second (mb_did mb) (mb_id mb, mb_addr mb, SIZEOF_BUF) (mb_did mb, mb_data mb, yb_len b) REST eq_refl ND) in HP, HK2.
    pose proof (ystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS1.
    pose proof (ystatics_pres _ _ _ _ YS1 HP) as YS2. clear YS YS1.
    pose proof (ypres_frame _ _ _ _ _ _ HP FR ltac:(lia)) as FR2. clear FR.
    pose proof (ypres_block _ _ _ _ _ _ HP YAF ltac:(exists hb; split; [right; exact HBIN| cbn; lia])) as YAF2. clear YAF.
    pose proof (ypres_block _ _ _ _ _ _ HP BC ltac:(eexists; split; [left; reflexivity| cbn; unfold SIZEOF_BUF; lia])) as BC2. clear BC.
    assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
    { eapply ry_pres_trans.
      - eapply ryajl_pres_of_munch; [exact MU| exact WM|].
        intros a Ha Hc _. cbn. split; [| exact I].
        destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
        pose proof (all_range_In _ _ RNG (or_intror (or_intror Hb))) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia.
      - eapply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP| lia| intros b0 Hb0; right; exact Hb0]. }
    clear MU WM MI HK1 AX1 AX ERR STK HP.
    (* [comment removed for export] *)
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
    rz_seg HKS HK2.
    step. step. step. step. step. step. step. step.
    apply evt_done. release_frame FR2 STK2 (bv_unsigned sp).
    (* [comment removed for export] *)
    eapply YWF with (p := mb_id mb) (A := mb_addr mb) (n := SIZEOF_BUF);
      [exact K0 | exact HK2 | left; reflexivity | exact AX2 | lia | exact STK2 | exact CEIL
      | unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR2
      | exact MI2 | exact TP | reflexivity | ].
    cbv beta. intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 mo3 s3' MI3 STK3 ERR3 AX3 HP3 HK3.
    assert (ND2 : List.NoDup (map blk_id ((mb_id mb, mb_addr mb, SIZEOF_BUF) :: REST))).
    { cbn [map] in ND |- *. inversion ND as [|x l NI NDl]; subst. inversion NDl; subst.
      constructor; [intros Hin; apply NI; right; exact Hin| assumption]. }
    rewrite (lb_remove_head (mb_id mb, mb_addr mb, SIZEOF_BUF) REST ND2) in HP3, HK3.
    eapply CONT. unfold ybuf_free_rpost.
    split; [| split; [eapply ypres_block; [exact HP3| exact YAF2| exists hb; split; [exact HBIN| cbn; lia]]
                    | apply RYST_split; split; [exact HK3| eapply ystatics_pres; [exact YS2| exact HP3]]]].
    split; [exact MI3|]. split; [exact STK3|]. split; [eexists; exact ERR3|]. split; [exact AX3|].
    eapply ry_pres_trans; [exact PRES2|]. apply ry_pres_of_rheap_pres. exact HP3.
  - (* [comment removed for export] *)
    assert (D0 : mb_data mb = 0) by (apply DZ; reflexivity).
    unfold buf_blocks in *. rewrite HD in *. cbn [app] in HK0, RNG, SEP, ND, HBIN'.
    clear BD.
    rz_seg HKS HK0.
    step. carve_frame 16%nat STK. step. step.
    step. if_cases K1; zify_cond K1. 1:{ kill K1. }
    step. step.
    step. if_cases K2; zify_cond K2. 2:{ kill K2. }
    step. step. step. step. step. step. step. step.
    apply evt_done. release_frame FR STK (bv_unsigned sp).
    destruct (yown_writes HK HKF _ _ _ _ _ _ B HK0 AX MU WM) as [HK1 AX1].
    { constructor; [| constructor]. left. cbn. unfold alloc_ceiling. lia. }
    { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    pose proof (ystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS1.
    eapply YWF with (p := mb_id mb) (A := mb_addr mb) (n := SIZEOF_BUF);
      [exact K0 | exact HK1 | left; reflexivity | exact AX1 | lia | exact STK | exact CEIL
      | unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR
      | exact MI | exact TP | reflexivity | ].
    cbv beta. intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m3 mo3 s3' MI3 STK3 ERR3 AX3 HP3 HK3.
    rewrite (lb_remove_head (mb_id mb, mb_addr mb, SIZEOF_BUF) REST ND) in HP3, HK3.
    eapply CONT. unfold ybuf_free_rpost.
    split; [| split; [eapply ypres_block; [exact HP3| exact YAF| exists hb; split; [exact HBIN| cbn; lia]]
                    | apply RYST_split; split; [exact HK3| eapply ystatics_pres; [exact YS1| exact HP3]]]].
    split; [exact MI3|]. split; [exact STK3|]. split; [eexists; exact ERR3|]. split; [exact AX3|].
    eapply ry_pres_trans; [| apply ry_pres_of_rheap_pres; exact HP3].
    eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. cbn. split; [| exact I].
    destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
    pose proof (all_range_In _ _ RNG (or_intror Hb)) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia.
Qed.
End S.
End RC__1.
