(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_W5_icb Th_errno Th_tsd Th_key Th_once Th_mutex Fz_T_atomic Fz_T_once Fz_T_lock Fz_T_local Fz_T_initthread Fz_T_master1 Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_errload Fz_I1_crypto Fz_I3_shelve Fz_I3_loadstrw Fz_I3_loadstr Fz_I3_ibasew Fz_I3_ibase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).

Definition OPT_LOAD_STRINGS : Z := 2.          (* [comment removed for export] *)
Definition SITE_icf_ibase : Z := 0x1f3748.      (* [comment removed for export] *)
Definition SITE_icf_ls : Z := 0x1f37b0.         (* [comment removed for export] *)
Definition SITE_icf_or : Z := 0x1f3964.         (* [comment removed for export] *)
Definition G_LS_ONCE : Z := 0xb9f300.
Definition ICF_PC : Z := 0x1f3600.              (* [comment removed for export] *)
Definition ICF_DESCR : Z := 0x474dc.

Definition if_w1_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word) (f lo pad : Z) (oldcb canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' a1' a2' a3' : word) (j8 rj fa fb : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128)) gp tp t0 t1 t2 (Z_to_bv 64 G_IC_BASE_ONCE) (Z_to_bv 64 e_ibase)
                 a0' a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 1)
                 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_ibase) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 24); (f + 32, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8);
              (bv_unsigned sp + -96 - pad + -128, bv_unsigned sp + -96 - pad + 8); (G_IC_BASE_ONCE, G_IC_BASE_ONCE + 4); (TP_A + -96, TP_A + -88)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j8; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 ICF_DESCR); C8 (Z_to_bv 64 ICF_PC); CB 8 fa; C8 (Z_to_bv 64 0); CB 16 fb]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
                                             C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
    /\ rw_cells asegs m' G_IC_OPTSDONE [C8 (Z_to_bv 64 0)] /\ acc asegs m' G_IC_OPTSDONE 8
    /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128))]
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -128)
         (once_full_cells G_IC_BASE_ONCE oldcb canary s6 (Z_to_bv 64 (f + 32)) s4 (Z_to_bv 64 OPT_LOAD_STRINGS) (Z_to_bv 64 f)
                          (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)))
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -32) [CB 8 rj; C8 (Z_to_bv 64 RUN_ONCE_RET)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ibase)]
    /\ ssp_cells m' canary
    /\ stk asegs m' (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad + -128).

Lemma if_w1 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word) (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (fj sj : list byte) (oldcb canary : word),
  (pad = 0 \/ pad = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 240 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> tp = Z_to_bv 64 TP_A ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [C8 (Z_to_bv 64 0); C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  stk asegs m (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96) -> stk asegs m lo (bv_unsigned sp + -96 - pad) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 (Z_to_bv 64 0)] -> acc asegs m G_IC_OPTSDONE 8 ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 0)] ->
  ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  mem_inv asegs m ->
  evt asegs (if_w1_post sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s6 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' f lo pad oldcb canary m)
    (MS (mkR (Z_to_bv 64 SITE_icb_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 OPT_LOAD_STRINGS) s4 s5 s6 s7 (Z_to_bv 64 0x7fff8000) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_icb_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' F fc m f lo pad fj sj oldcb canary
    PADC FPOS FAL FBASE FTOP FSH LOSP LOHI SPTOP TPV IMGU SHCELL SAVED PADSTK LOWSTK FRMC SHDC STOPC ODONE ODACC BONCE SSPC CBUF MINV.
  subst tp.
  unfold g_shadow_memory_dynamic_address in SHCELL. unfold SITE_icb_smalloc, OPT_LOAD_STRINGS.
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(f, f + 24); (f + 32, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8);
                          (bv_unsigned sp + -96 - pad + -128, bv_unsigned sp + -96 - pad + 8); (12186304, 12186304 + 4); (TP_A + -96, TP_A + -88)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (acc_granule0_ro m 12186272 8 12186272 ODACC ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)) as ODSH.
  unfold shad, SHB in ODSH. change (12186272 / 8 + 2147450880) with 2148974164 in ODSH.
  destruct SSPC as [GOTC GUARDC]. unfold got_ssp, ssp_guard in GOTC, GUARDC.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  apply (rw_cells_split_CB asegs m f [] 56 fj [] [8; 8; 8; 8; 8; 8; 8]%nat) in FRMC; [|reflexivity]. cbn [mk_CB_cells app firstn skipn] in FRMC.
  apply (rw_cells_split_CB asegs m (f / 8 + 2147450880) [] 8 sj [] [1; 1; 1; 1; 1; 1; 1; 1]%nat) in SHDC; [|reflexivity]. cbn [mk_CB_cells app firstn skipn] in SHDC.
  zstep. zstep. zstep.
  zstep. if_cases BR; zify_cond BR; [clear BR| exfalso; lia].
  do 8 zstep.
  zstep. th_fix_lit_store.
  zstep. th_fix_lit_store.
  zstep. th_fix_lit_store.
  zstep.
  replace (Z.shiftr f 3) with (f / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  zstep. th_fix_lit_store.
  zstep. rewrite th_le1_mod. mem_after_store.
  zstep. rewrite th_le1_mod. mem_after_store.
  zstep. rewrite th_le1_mod. mem_after_store.
  zstep.
  zstep. rewrite th_le1_mod. mem_after_store.
  zstep. rewrite th_le1_mod. mem_after_store.
  zstep. rewrite th_le1_mod. mem_after_store.
  zstep. rewrite th_le1_mod. mem_after_store.
  zstep. zstep.
  destruct PADC as [PZ|PZ]; subst pad.
  1: replace (bv_unsigned sp + -96 - 0) with (bv_unsigned sp + -96) in * by lia.
  2: replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) in * by lia.
  2: th_frame 16%nat [8; 8]%nat PADSTK; rename FR into PADFR, junk into padj.
  all: zstep.
  all: zstep; th_if_lit.
  all: do 6 zstep.
  all: zstep.
  all: th_frame 16%nat [8; 8]%nat LOWSTK.
  all: do 6 (zstep; th_fix_lit_store).
  all: do 3 zstep.
  all: zstep; th_if_lit.
  all: do 3 zstep.
  all: replace (Z.shiftr (f + 32) 3) with (f / 8 + 4) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  all: do 2 zstep.
  all: zstep; th_if_lit.
  all: do 6 (zstep; th_fix_lit_store).
  all: zstep. all: zstep; th_if_lit.
  all: do 2 zstep. all: zstep; th_if_lit.
  all: do 5 zstep.
  1: release_frame FR LOWSTK (bv_unsigned sp + -96).
  2: release_frame FR LOWSTK (bv_unsigned sp + -112).
  all: tcall (T_run_once_enter_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 2046728 oldcb canary).
  all: try (solve [assumption | reflexivity | unfold got_ssp, ssp_guard; lia | unfold ssp_cells, got_ssp, ssp_guard; split; assumption]).
  all: rename MI into MINV2, PC into STK2, PC0 into SSP2, PC1 into BRUN, PC2 into CBNEW, PC3 into FULL2, PC4 into RET2, POST into LINK2.
  all: apply evt_done; unfold if_w1_post.
  1: replace (bv_unsigned sp + -96 - 0) with (bv_unsigned sp + -96) by lia.
  2: replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) by lia.
  all: unfold G_IC_BASE_ONCE, G_IC_OPTSDONE, e_ibase, ICF_DESCR, ICF_PC, OPT_LOAD_STRINGS, SITE_icf_ibase.
  all: assert (E15 : Z_to_bv 8 (-15 mod 256) = Z_to_bv 8 (-15)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
  all: assert (E13 : Z_to_bv 8 (-13 mod 256) = Z_to_bv 8 (-13)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
  all: rewrite E15, E13 in SHDC.
  all: pose proof (rw_cells_merge asegs _ f [_; _; _; _; _] [_; _] [] FRMC) as FR56; cbn [cells_size csize Nat.add app] in FR56.
  all: lazymatch type of MU with munch _ _ ?mf => assert (ODACC2 : acc asegs mf 12186272 8)
         by (apply (acc_agree _ _ 12186272 8 ODACC ltac:(lia)); intros ad INSH; cbv beta in INSH; unfold shad, SHB in INSH; apply MU; cbn [outside];
             repeat split; try exact I; lia) end.
  all: pose proof (rw_cells_blur _ _ [_] _ SAVED) as SAVEDB; cbn [cells_size csize Nat.add] in SAVEDB.
  2: release_frame PADFR PADSTK (bv_unsigned sp + -96).
  all: do 9 eexists.
  all: split; [reflexivity|].
  all: split; [exact MU|]. all: split; [exact WM|]. all: split; [exact MINV2|].
  all: split; [exact SAVEDB|]. all: split; [exact FR56|]. all: split; [exact SHDC|].
  all: split; [exact ODONE|]. all: split; [exact ODACC2|].
  all: split; [exact BRUN|]. all: split; [exact CBNEW|]. all: split; [exact FULL2|]. all: split; [exact RET2|]. all: split; [exact LINK2|].
  all: split; [exact SSP2|]. all: split; [exact PADSTK|exact STK2].
Qed.

(* [comment removed for export] *)
Definition if_w2_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f lo pad : Z) (oldcb canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' a1' a2' a3' : word) (rj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128)) gp tp t0 t1 t2 (Z_to_bv 64 G_LS_ONCE) (Z_to_bv 64 e_loadstr)
                 a0' a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) (Z_to_bv 64 1)
                 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_loadstr) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -96 - pad + -160, bv_unsigned sp + -96 - pad); (G_IC_BASE_ONCE, G_IC_BASE_ONCE + 4); (G_LS_ONCE, G_LS_ONCE + 4);
              (TP_A + -96, TP_A + -88)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)]
    /\ rw_cells asegs m' G_LS_ONCE [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128))]
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -128)
         (once_full_cells G_LS_ONCE oldcb canary (Z_to_bv 64 1) (Z_to_bv 64 (f + 32)) s4 (Z_to_bv 64 OPT_LOAD_STRINGS) (Z_to_bv 64 f)
                          (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)))
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -32) [CB 8 rj; C8 (Z_to_bv 64 RUN_ONCE_RET)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ls)]
    /\ ssp_cells m' canary
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad + -128).

Lemma if_w2 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (junk : list byte) (oldcb canary cb : word),
  (pad = 0 \/ pad = 16) -> 0 < f -> f + 64 <= lo ->
  lo <= bv_unsigned sp - 272 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> tp = Z_to_bv 64 TP_A ->
  img_untouched m ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 1)] -> ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 cb] ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -128) (once_full_cells G_IC_BASE_ONCE oldcb canary s6 (Z_to_bv 64 (f + 32)) s4 (Z_to_bv 64 OPT_LOAD_STRINGS) (Z_to_bv 64 f)
                                                          (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 (bv_unsigned sp + -96 - pad))) ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)] ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ibase)] ->
  stk asegs m lo (bv_unsigned sp + -96 - pad + -128) ->
  rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] -> rw_cells asegs m G_LS_ONCE [C4 (Z_to_bv 64 0)] ->
  mem_inv asegs m ->
  evt asegs (if_w2_post sp gp tp t0 t1 t2 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 F fc f lo pad oldcb canary m)
    (MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128)) gp tp t0 t1 t2 (Z_to_bv 64 G_IC_BASE_ONCE) (Z_to_bv 64 e_ibase)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2)
             (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ONCE_RET_INIT) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s10 s11 t3 t4 t5 t6 F fc m f lo pad junk oldcb canary cb
    PADC FPOS FTOP LOSP LOHI SPTOP TPV IMGU BONCE1 SSPC CBUF FULLC RETC LINKC LOWSTK BRET LSONCE0 MINV.
  subst tp.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp + -96 - pad + -160, bv_unsigned sp + -96 - pad); (G_IC_BASE_ONCE, G_IC_BASE_ONCE + 4); (G_LS_ONCE, G_LS_ONCE + 4);
                          (TP_A + -96, TP_A + -88)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold G_IC_BASE_ONCE, G_IC_BASE_RET, G_LS_ONCE in *.
  tcall (T_run_once_leave_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -96 - pad) 12186304 cb oldcb canary
           (Z_to_bv 64 SITE_icf_ibase) sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 f) (Z_to_bv 64 OPT_LOAD_STRINGS) s4 (Z_to_bv 64 (f + 32)) s6 junk).
  all: try (solve [assumption | unfold got_ssp, ssp_guard; lia]).
  rename MI into MINV1, PC into STK1, PC0 into SSP1, PC1 into BDONE, POST into CBOLD.
  unfold SITE_icf_ibase. try th_ret_lit.
  zstep; th_if_lit.
  zstep. zstep. zstep; th_if_lit.
  zstep. zstep. zstep; th_if_lit.
  zstep; th_if_lit.
  zstep. zstep; th_if_lit.
  zstep. zstep; th_if_lit.
  do 5 zstep.
  tcall (T_run_once_enter_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 2046940 oldcb canary).
  all: try (solve [assumption | reflexivity | unfold got_ssp, ssp_guard; lia]).
  rename MI into MINV2, PC into STK2, PC0 into SSP2, PC1 into LSRUN, PC2 into CBNEW, PC3 into FULL2, PC4 into RET2, POST into LINK2.
  apply evt_done. unfold if_w2_post, G_IC_BASE_ONCE, G_LS_ONCE, e_loadstr, OPT_LOAD_STRINGS, SITE_icf_ls.
  do 6 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MINV2|].
  split; [exact BDONE|]. split; [exact LSRUN|]. split; [exact CBNEW|]. split; [exact FULL2|].
  split; [exact RET2|]. split; [exact LINK2|]. split; [exact SSP2| exact STK2].
Qed.

(* [comment removed for export] *)
Definition if_w3_post (sp gp tp t0 t1 t2 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f lo pad : Z) (oldcb canary : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' a1' a2' a3' a4' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_icf_or) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 a0' a1' a2' a3' a4' a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 OPT_LOAD_STRINGS) s4 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 1) (Z_to_bv 64 1)
                 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f3aa0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -96 - pad + -160, bv_unsigned sp + -96 - pad); (G_LS_ONCE, G_LS_ONCE + 4); (TP_A + -96, TP_A + -88);
              (G_IC_OPTSDONE, G_IC_OPTSDONE + 8); (f, f + 8); (f + 32, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' G_LS_ONCE [C4 (Z_to_bv 64 2)]
    /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' G_IC_OPTSDONE [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)]
    /\ rw_cells asegs m' (f + 32) [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 0x45e0360e)]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11));
                                             C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11))]
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad).

Lemma if_w3 : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (f lo pad p1 : Z) (junk : list byte) (oldcb canary cb mg : word) (b5 b6 b7 : byte),
  (pad = 0 \/ pad = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 272 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> tp = Z_to_bv 64 TP_A ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m G_LS_ONCE [C4 (Z_to_bv 64 1)] -> ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 cb] ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -128) (once_full_cells G_LS_ONCE oldcb canary (Z_to_bv 64 1) (Z_to_bv 64 (f + 32)) s4 (Z_to_bv 64 OPT_LOAD_STRINGS) (Z_to_bv 64 f)
                                                          (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 (bv_unsigned sp + -96 - pad))) ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)] ->
  rw_cells asegs m (bv_unsigned sp + -96 - pad + -16) [C8 sp; C8 (Z_to_bv 64 SITE_icf_ls)] ->
  stk asegs m lo (bv_unsigned sp + -96 - pad + -128) ->
  rw_cells asegs m G_LS_RET [C4 (Z_to_bv 64 1)] -> rw_cells asegs m G_IC_OPTS_LOCK [C8 (Z_to_bv 64 p1)] -> 0 <= p1 < 2^64 ->
  rw_cells asegs m G_IC_OPTSDONE [C8 (Z_to_bv 64 0)] -> acc asegs m G_IC_OPTSDONE 8 ->
  rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 b5; C1 b6; C1 b7] ->
  rw_cells asegs m f [C8 mg] ->
  mem_inv asegs m ->
  evt asegs (if_w3_post sp gp tp t0 t1 t2 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 F fc f lo pad oldcb canary m)
    (MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -96 - pad + -128)) gp tp t0 t1 t2 (Z_to_bv 64 G_LS_ONCE) (Z_to_bv 64 e_loadstr)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2)
             (Z_to_bv 64 1) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ONCE_RET_INIT) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 s11 t3 t4 t5 t6 F fc m f lo pad p1 junk oldcb canary cb mg b5 b6 b7
    PADC FPOS FAL FBASE FTOP FSH LOSP LOHI SPTOP TPV IMGU SHCELL LSRUN SSPC CBUF FULLC RETC LINKC LOWSTK LSRET LOCKC LOCKR ODONE ODACC TMPC SHDC MAGC MINV.
  subst tp.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp + -96 - pad + -160, bv_unsigned sp + -96 - pad); (G_LS_ONCE, G_LS_ONCE + 4); (TP_A + -96, TP_A + -88);
                          (G_IC_OPTSDONE, G_IC_OPTSDONE + 8); (f, f + 8); (f + 32, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold G_LS_ONCE, G_LS_RET, G_IC_OPTS_LOCK, G_IC_OPTSDONE in *.
  unfold g_shadow_memory_dynamic_address in SHCELL.
  pose proof (acc_granule0_ro m 12186272 8 12186272 ODACC ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)) as ODSH.
  unfold shad, SHB in ODSH. change (12186272 / 8 + 2147450880) with 2148974164 in ODSH. clear ODACC.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  tcall (T_run_once_leave_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -96 - pad) 12186368 cb oldcb canary
           (Z_to_bv 64 SITE_icf_ls) sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) (Z_to_bv 64 f) (Z_to_bv 64 OPT_LOAD_STRINGS) s4 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 1) junk).
  all: try (solve [assumption | unfold got_ssp, ssp_guard; lia]).
  rename MI into MINV1, PC into STK1, PC0 into SSP1, PC1 into LSDONE, POST into CBOLD.
  destruct SSP1 as [GOT1 GUARD1]. unfold got_ssp, ssp_guard in GOT1, GUARD1.
  unfold SITE_icf_ls. try th_ret_lit.
  zstep; th_if_lit.
  zstep. zstep. zstep; th_if_lit.
  do 10 (zstep; zstep; th_if_lit).
  do 7 zstep.
  zstep. th_frame 16%nat [8; 8]%nat STK1.
  do 2 (zstep; th_fix_lit_store).
  do 7 zstep.
  zstep; th_if_lit.
  assert (AMOAL : amo_aligned AD (Z_to_bv 64 12186272) = true) by (vm_compute; reflexivity).
  th_amo_step AMOAL.
  zstep.
  replace (Z.shiftr (f + 32) 3) with (f / 8 + 4) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  do 2 zstep.
  zstep; th_if_lit.
  zstep. zstep.
  zstep; th_fix_lit_store.
  do 4 zstep.
  release_frame FR STK1 (bv_unsigned sp + -96 - pad).
  zstep. zstep. zstep.
  zstep; rewrite th_le1_mod; mem_after_store.
  zstep. zstep.
  zstep; th_fix_lit_store.
  zstep. if_cases BR; zify_cond BR; [exfalso; lia| clear BR].
  zstep.
  do 8 (zstep; rewrite th_le1_mod; mem_after_store).
  apply evt_done. unfold if_w3_post, G_LS_ONCE, G_IC_OPTSDONE, OPT_LOAD_STRINGS, SITE_icf_or.
  assert (E11 : Z_to_bv 8 (-11 mod 256) = Z_to_bv 8 (-11)) by (apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
  rewrite E11 in SHDC.
  assert (EOR : amo_val AMO_OR (Z_to_bv 64 0) (Z_to_bv 64 2) = Z_to_bv 64 2) by (apply bv_eq; vm_compute; reflexivity).
  unfold OPT_LOAD_STRINGS in ODONE, TMPC. rewrite EOR in ODONE.
  change (Z.lor 0 (Z.land 2 18446744073709551615)) with 2 in TMPC.
  do 6 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MINV1|].
  split; [exact LSDONE|]. split; [exact CBOLD|]. split; [exact (conj GOT1 GUARD1)|].
  split; [exact ODONE|]. split; [exact TMPC|]. split; [exact MAGC|]. split; [exact SHDC| exact STK1].
Qed.
