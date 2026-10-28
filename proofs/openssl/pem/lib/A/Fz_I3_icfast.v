(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Str_cpy Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_T_atomic Fz_T_once Fz_W5_icb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Definition icf1_post (sp gp tp s4 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word) (f opts lo pad : Z) (od : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7x t3 t4 t5 t6 : word) (j : list byte) (m' : mem),
    ms = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 opts) s4 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 1) s7x (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_icb_release) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp - 128, bv_unsigned sp - 88)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ stk asegs m' (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad)
    /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od].

Lemma icf1_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word) (F : bvmap 5 word) fc (m : mem) (f lo pad opts : Z) (fj sj : list byte) (od : word),
  (pad = 0 \/ pad = 16) -> 0 <= opts < 2^64 -> Z.land (bv_unsigned od) opts = opts -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 128 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0); C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  stk asegs m (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96) -> stk asegs m lo (bv_unsigned sp + -96 - pad) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] -> acc asegs m G_IC_OPTSDONE 8 ->
  mem_inv asegs m ->
  evt asegs (icf1_post sp gp tp s4 s10 s11 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' f opts lo pad od m)
    (MS (mkR (Z_to_bv 64 SITE_icb_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 opts) s4 s5 s6 s7 (Z_to_bv 64 0x7fff8000) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_icb_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until od. intros HP HO DONE F0 F64 FIMG FLO FSH HLO HLOS SPH UT SHC FR GAP ST FB SB STP OD ACCO MI.
  unfold SITE_icb_smalloc, G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 128, SP - 88)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 128, SP - 88)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  do 3 zstep. zstep. if_true.
  do 4 zstep. rewrite (shr3_div f) by lia.
  do 4 zstep.
  zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. zstep. cbv beta.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app _ f [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 292060); C8 (Z_to_bv 64 2045440)] _)) in FB.
  destruct FB as [FBH FBT]. cbn [cells_size csize Nat.add] in FBT.
  remember (skipn 8 (skipn 8 (skipn 8 fj))) as fr eqn:Efr. clear Efr.
  apply (rw_cells_split_CB asegs _ (f + Z.of_nat 24) [] 32 fr [] [8; 8; 16]%nat) in FBT; [| reflexivity]. cbn [mk_CB_cells app] in FBT.
  assert (L8 : length (firstn 8 (skipn 8 fr)) = 8%nat) by (destruct FBT as [[WF _] _]; cbn in WF; tauto).
  apply (th_cells_congr asegs _ (f + Z.of_nat 24) _ [CB 8 (firstn 8 fr); C8 (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 8 fr)))); CB 16 (firstn 16 (skipn 8 (skipn 8 fr)))]) in FBT;
    [| cbn [cells_bytes cbytes]; rewrite (le8_ld _ L8); reflexivity | reflexivity | cbn; destruct FBT as [[WF _] _]; cbn in WF; tauto].
  replace (f + Z.of_nat 24) with (f + 24) in FBT by lia.
  apply (proj1 (rw_cells_app _ (f + 24) [CB 8 (firstn 8 fr)] _)) in FBT. destruct FBT as [FB24 FBT]. cbn [cells_size csize Nat.add] in FBT.
  apply (proj1 (rw_cells_app _ _ [C8 (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 8 fr))))] _)) in FBT. destruct FBT as [TMP FB40].
  cbn [cells_size csize Nat.add] in FB40. replace (f + 24 + Z.of_nat 8) with (f + 32) in TMP, FB40 by lia. replace (f + 32 + Z.of_nat 8) with (f + 40) in FB40 by lia.
  remember (bv_extract 0 64 (le_bytes_to_word (firstn 8 (skipn 8 fr)))) as w32 eqn:Ew. clear Ew L8.
  (* [comment removed for export] *)
  destruct HP as [-> | ->].
  1: replace (SP + -96 - 0) with (SP + -96) in * by lia.
  2: replace (SP + -96 - 16) with (SP + -112) in * by lia; carve_frame 16%nat GAP.
  all: zstep.
  all: zstep; th_if_lit.
  all: do 5 zstep; zstep.
  (* [comment removed for export] *)
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (VA1 : acc asegs mX 12186272 8)
      by (apply (acc_agree m mX _ _ ACCO ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside]; lia);
    assert (SB4 : rw_cells asegs mX (f / 8 + 2147450880 + 4) [C1 (Z_to_bv 8 0)])
      by (exact (rw_cells_head mX _ _ _ (rw_cells_skip mX (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ SB)));
    assert (RA1 : acc asegs mX (f + 32) 8)
      by (apply (acc_of_shadow0 mX (f + 32)); [replace (shad (f + 32)) with (f / 8 + 2147450880 + 4) by (unfold shad, SHB; Z.div_mod_to_equations; lia); exact (rw_C1_bytes mX _ _ SB4)
                                            | Z.div_mod_to_equations; lia | lia])
  end.
  all: tcall (T_atomic_load_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo od w32);
    [ exact (proj1 OD) | exact VA1 | reflexivity | exact TMP | exact RA1 | Z.div_mod_to_equations; lia | lia | unfold IMG_UT_LO, IMG_UT_HI; right; lia
    | clear - FSH; lia | exact (ut_munch _ m _ UT MU HWU) | exact SHC | eassumption | lia | lia | lia | lia | lia | assumption | ].
  all: cbv beta delta [mkR]; clear VA1 SB4 RA1 PC0.
  all: zstep. all: zstep; th_if_lit. all: do 3 zstep.
  (* [comment removed for export] *)
  all: if_cases KOD; zify_cond KOD; [exfalso; rewrite ?unsigned_lit in KOD by lia; lia | zstep; zstep].
  (* [comment removed for export] *)
  all: zstep; (zstep; lfix); zstep; zstep; (zstep; lfix).
  all: zstep; if_cases KF2; zify_cond KF2; [exfalso; lia|].
  all: zstep; do 8 (zstep; lfix).
  (* [comment removed for export] *)
  all: pose proof (rw_cells_blur _ _ [_] _ FR) as FRB; cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: try match goal with H : rw_cells _ _ ?a [C8 _; CB 8 _], G : stk _ _ ?a ?a |- _ => release_frame H G (bv_unsigned sp + -96) end.
  all: unfold icf1_post, SITE_icb_release.
  all: try replace (bv_unsigned sp + -96 - 0) with (bv_unsigned sp + -96) by lia.
  all: try replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) by lia.
  all: apply evt_done; do 19 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FRB|]; split; [eassumption|]; split; [eassumption| exact OD].
Qed.

Section CIcf.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis GO_optsdone : GOBJ G_IC_OPTSDONE 8.

(* [comment removed for export] *)
Definition init_crypto_fast_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (od : word) (opts : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 opts -> 0 <= opts < 2^64 -> Z.land (bv_unsigned od) opts = opts ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 128 <= bv_unsigned sp ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_init_crypto m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od]) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem init_crypto_fast_cps : init_crypto_fast_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo od opts
    FDO MST -> -> HO DONE ART0 MI0 CALL HSTK Hfr Hcr STP OD.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pad := usp mod 32).
  assert (HP : pad = 0 \/ pad = 16) by (unfold pad; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pad) by reflexivity. clearbody pad.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 128 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -96 - pad).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in *.
  (* [comment removed for export] *)
  pose proof (icb_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad opts
                HP HPM HO ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_icb_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 opts) a1 s5 s6 s7 (Z_to_bv 64 0x7fff8000) s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl Hfr Hcr ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_icb_smalloc) in Hc2' by (unfold SITE_icb_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & _).
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m1 m2 _ _ GAP1). intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  (* [comment removed for export] *)
  assert (AGS02 : forall a k, (0xb9f200 <= a /\ a + k <= 0xb9f848) -> agree_on (fun x => a <= x < a + k) m m2).
  { intros a k H x Hx. cbv beta in Hx. rewrite (PRES2 x ltac:(right; left; apply client_static_intro; lia)). apply PR1; [right; left; apply client_static_intro; lia | exact I]. }
  assert (WM02 : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM2).
  assert (STP2 : rw_cells asegs m2 0xb9f200 [C1 (Z_to_bv 8 0)]) by (apply (rw_cells_agree asegs m m2 _ _ STP); [apply AGS02; cbn [cells_size csize Nat.add]; lia | exact WM02]).
  assert (OD2 : rw_cells asegs m2 0xb9f2a0 [C8 od]) by (apply (rw_cells_agree asegs m m2 _ _ OD); [apply AGS02; cbn [cells_size csize Nat.add]; lia | exact WM02]).
  pose proof (afp_acc_global RT GOBJ AFP Σ1 m2 _ _ 0xb9f2a0 8 ART2 GO_optsdone ltac:(unfold G_IC_OPTSDONE; lia) ltac:(unfold G_IC_OPTSDONE; lia)) as ACCO2.
  (* [comment removed for export] *)
  pose proof (icf1_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 a1 s5 s6 s7 s9 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F2 fc2 m2 f lo pad opts fj sj od HP HO DONE F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia)
                ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                UT2 SHC2 FR2 GAP2 ST2 FB2 SB2 STP2 OD2 ACCO2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (ra1 & v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & s7x & v3 & v4 & v5 & v6 & j3 & m3 & -> & MU3 & WM3 & MI3 & FR3 & GAP3 & ST3 & OD3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, GAP3, Hc3'. fold usp1 in GAP3, ST3, Hc3'.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 128) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - apply acl_stack. unfold USTACK_TOP in *. lia. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ1 m3 f 0%nat (rt_frames RT Σ) ART3 FRS1) as (Σ3 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP1 in FLW.
  (* [comment removed for export] *)
  pose proof (icb_s2_walk ra1 ra sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 d0 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 opts) a1 (Z_to_bv 64 (f + 32)) s7x
                (Z_to_bv 64 (f / 8 + 2147450880)) s10 s11 v3 v4 v5 v6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F2 fc2 m3 f fl lo pad j3
                HP ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                F0 ltac:(lia) FL0 ltac:(lia) ST3 GAP3 FR3 FW FLC MI3) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (y0 & y1 & y2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FLC4) & Hc4'). clear Hc4.
  fold usp in ST4.
  destruct (REL m4 MU4 WM4 FLC4) as (ART4 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).
  (* [comment removed for export] *)
  assert (NFL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> x <> fl).
  { intros x Hx E. subst x. destruct Hx as [H|H]; [unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia|]. apply NAC. right. rewrite LV1, FRS1.
    destruct H as [H|[H|[H|H]]]; [left; exact H | right; left; exact H
      | right; right; left; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]
      | right; right; right; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]]. }
  assert (AG4 : forall a k, (forall x, a <= x < a + k -> x <> fl) -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H. apply (agree_of_munch _ m3 m4 _ MU4). intros x Hx. cbv beta in Hx. specialize (H x Hx). cbn [outside]. lia. }
  assert (AG3 : forall a k, (usp <= a /\ a + k <= USTACK_TOP) \/ (0x10000 <= a /\ a + k <= 0xbc6000) -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H. apply (agree_of_munch _ m2 m3 _ MU3). intros x Hx. cbv beta in Hx. cbn [outside]. pose proof (div8_facts f). unfold USTACK_TOP, RT_STACK in *. lia. }
  apply Hk. exists Σ3.
  split; [| split; [rewrite LV3; exact LV1 | split; [exact FRS3 | split; [rewrite SP3; exact SP1 | split; [rewrite CR3; exact CR1 | rewrite CG3; exact CG1]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ1 Σ3 PMc _ c4 Hc4' AL3 AM3)|]. intros ms <-. exists m4.
  split; [exists y0, y1, y2, g1, g2, g3, g4, g5, g6, g7, y3, y4, y5, y6, F2, fc2; reflexivity|].
  split; [split; [exact ART4 | split; [exact MI4 | split; [exact (wmono_trans asegs _ _ _ WM02 (wmono_trans asegs _ _ _ WM3 WM4)) | exact ST4]]]|].
  assert (STAT : forall a cs, 0xb9f200 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f848 -> rw_cells asegs m2 a cs -> rw_cells asegs m4 a cs).
  { intros a cs H1 H2 H. apply (rw_cells_agree asegs m3 m4); [apply (rw_cells_agree asegs m2 m3 _ _ H); [| exact WM3] | | exact WM4].
    - apply AG3. right. lia.
    - apply AG4. intros x Hx. apply NFL. right; left. apply client_static_intro. lia. }
  split.
  { intros a Ha.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Ha) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    pose proof (cl_split RT AF Σ m usp 128 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
    pose proof (NFL _ Ha) as N5.
    rewrite (MU4 a ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (MU3 a ltac:(cbn [outside]; clear - N1 N2 N4 HP; lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | unfold usp1; lia])).
    exact (PR1 a Ha I). }
  split; [apply STAT; [lia | cbn [cells_size csize Nat.add]; lia | exact STP2]|].
  apply STAT; [lia | cbn [cells_size csize Nat.add]; lia | exact OD2].
Qed.

End CIcf.
