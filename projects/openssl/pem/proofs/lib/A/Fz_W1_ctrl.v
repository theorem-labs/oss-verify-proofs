(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_W1_defs Fz_W1_new Fz_W1_sync Fz_ukit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Export Fz_W1_pploc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition SITE_ctrl_sync : Z := 0x3049d4.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ctrl_frame (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition ci_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (v : word) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (k0 k1 k2 r1 r2 r3 r4 r5 r6 r7 k3 k4 k5 k6 : word) (mf : mem),
    ms = MS (mkR ra0 sp gp tp k0 k1 k2 s0' s1' v r1 r2 r3 r4 r5 r6 r7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 k3 k4 k5 k6) F (ret_pc ra0) fc None mf (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m mf /\ wmono asegs m mf /\ mem_inv asegs mf /\ stk asegs mf lo (bv_unsigned sp).

Lemma ci_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a2 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R fl : Z) (iw shw rrw numw padw rlw rdw rmaxw rflw : word),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  rw_cells asegs m R [C8 rlw; C8 rdw; C8 rmaxw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  mem_inv asegs m ->
  evt asegs (ci_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc rlw lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 3) a2 (Z_to_bv 64 0) a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros until rflw. intros SPLO LOHI SPHI STK UNT SHB BIOW FLOK BIACC BIPOS BIAL BIHI BILO BBC BBACC BBPOS BBAL BBHI BBLO BMACC BMPOS BMAL BMHI BMLO RCL RACC RPOS RAL RHI RLO MINV.
  unfold e_mem_ctrl, ci_post in *.
  assert (SHADLIT : ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)]) by exact SHB. clear SHB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.of_N] in SPR.
  remember (bv_unsigned sp) as U eqn:EU. rewrite <- (Z_to_bv_bv_unsigned sp), <- EU.
  pose proof (munch_refl [(U - 80, U)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(U - 80, U)]) by ut_fp_lia. assert (HWS : sh_fp [(U - 80, U)]) by sh_fp_lia.
  unfold bio_w1_cells in BIOW. destruct FLOK as (FLR & FLM).
  assert (BI8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  assert (BB8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (BM8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  assert (R8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat STK.
  do 11 zstep. do 9 (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit).
  do 7 (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit).
  (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit). zstep. zstep.
  rewrite (zx32_small fl) by lia. rewrite (unsigned_lit fl) by lia. rewrite FLM.
  repeat (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit).
  th_release FR U.
  subst U. rewrite ?Z_to_bv_bv_unsigned. apply evt_done.
  do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition cp_s0_post (sp gp tp a2 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word)
    (BI BB BM R PP fl lo : Z) (rlw rdw : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (mf : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ctrl_sync) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp (Z_to_bv 64 ((BI + 48) ≫ 3 + 2147450880)) rlw (Z_to_bv 64 ((R + 8) ≫ 3 + 2147450880))
                 sp a2 (Z_to_bv 64 BI) (Z_to_bv 64 115) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 (R + 8)) (Z_to_bv 64 (BM + 8)) (Z_to_bv 64 fl) (Z_to_bv 64 0)
                 (Z_to_bv 64 BB) (Z_to_bv 64 PP) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 1) (Z_to_bv 64 BI) (Z_to_bv 64 2147450880) s8 s9 s10 s11
                 (Z_to_bv 64 (R ≫ 3 + 2147450880)) rdw (Z_to_bv 64 127) t6)
            F (Z_to_bv 64 e_mem_buf_sync) fc None mf (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m mf /\ wmono asegs m mf /\ mem_inv asegs mf
    /\ rw_cells asegs mf (bv_unsigned sp + -80) (CB 8 j :: ctrl_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs mf lo (bv_unsigned sp + -80).

Lemma cp_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a2 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R PP fl : Z) (iw shw rrw numw padw rlw rdw rmaxw rflw : word),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  rw_cells asegs m R [C8 rlw; C8 rdw; C8 rmaxw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  0 < PP < 2^64 -> mem_inv asegs m ->
  evt asegs (cp_s0_post sp gp (Z_to_bv 64 0xba3ef0) a2 s8 s9 s10 s11 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' BI BB BM R PP fl lo rlw rdw m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 115) a2 (Z_to_bv 64 PP) a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros until rflw. intros SPLO LOHI SPHI STK UNT SHB BIOW FLOK BIACC BIPOS BIAL BIHI BILO BBC BBACC BBPOS BBAL BBHI BBLO BMACC BMPOS BMAL BMHI BMLO RCL RACC RPOS RAL RHI RLO PPR MINV.
  unfold e_mem_ctrl, cp_s0_post in *.
  assert (SHADLIT : ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)]) by exact SHB. clear SHB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.of_N] in SPR.
  remember (bv_unsigned sp) as U eqn:EU. rewrite <- (Z_to_bv_bv_unsigned sp), <- EU.
  pose proof (munch_refl [(U - 80, U)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(U - 80, U)]) by ut_fp_lia. assert (HWS : sh_fp [(U - 80, U)]) by sh_fp_lia.
  unfold bio_w1_cells in BIOW. destruct FLOK as (FLR & FLM).
  assert (BI8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  assert (BB8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (BM8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  assert (R8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat STK.
  do 11 zstep. do 9 (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit).
  do 7 (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit).
  (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit). zstep. zstep.
  rewrite (zx32_small fl) by lia. rewrite (unsigned_lit fl) by lia. rewrite FLM.
  do 39 (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit).
  assert (PPNZ : bv_eqb (Z_to_bv 64 PP) z64 = false)
    by (unfold bv_eqb; rewrite (unsigned_lit PP) by lia; apply Z.eqb_neq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia).
  zstep. rewrite PPNZ. cbv iota.
  do 3 (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit).
  subst U. rewrite ?Z_to_bv_bv_unsigned. apply evt_done.
  exists (firstn 8 junk), m0. split; [unfold e_mem_buf_sync; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MINV|]. split; [exact FR| exact STK].
Qed.

(* [comment removed for export] *)
Definition cp_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (BM PP lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (k0 k1 k2 r1 r2 r3 r4 r5 r6 r7 k3 k4 k5 k6 : word) (mf : mem),
    ms = MS (mkR ra0 sp gp tp k0 k1 k2 s0' s1' (Z_to_bv 64 1) r1 r2 r3 r4 r5 r6 r7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 k3 k4 k5 k6) F (ret_pc ra0) fc None mf (seg_rom asegs)
    /\ munch [(PP, PP + 8)] m mf /\ wmono asegs m mf /\ mem_inv asegs mf /\ stk asegs mf lo (bv_unsigned sp)
    /\ rw_cells asegs mf PP [C8 (Z_to_bv 64 BM)].

Lemma cp_s1_walk : forall ra0 ra1 sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6 (s1x s4x s6x : word)
    (F : bvmap 5 word) fc (m : mem) (lo BB BM R PP : Z) (oldpp : word) (j : list byte),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -80) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -80) (CB 8 j :: ctrl_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo -> 0 <= BM < 2^64 ->
  rw_cells asegs m PP [C8 oldpp] -> acc asegs m PP 8 -> PP mod 8 = 0 -> 0 < PP -> (PP + 8 <= IMG_UT_LO \/ IMG_UT_HI <= PP) -> PP + 8 <= 2^47 -> (PP + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= PP) ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> mem_inv asegs m ->
  evt asegs (cp_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc BM PP lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1x a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 BB) (Z_to_bv 64 PP) s4x (Z_to_bv 64 1) s6x (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ctrl_sync) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros SPLO LOHI SPHI STK UNT FRM BBC BBACC BBPOS BBAL BBHI BBLO BMR PPC PPACC PPAL PPPOS PPUT PPTOP PPSH PPSTK MINV.
  unfold SITE_ctrl_sync, cp_s1_post in *. unfold ctrl_frame in FRM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.of_N] in SPR.
  remember (bv_unsigned sp) as U eqn:EU. rewrite <- (Z_to_bv_bv_unsigned sp), <- EU.
  pose proof (munch_refl [(PP, PP + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(PP, PP + 8)]) by ut_fp_lia. assert (HWS : sh_fp [(PP, PP + 8)]) by sh_fp_lia.
  assert (BB8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  do 23 (zstep; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try th_if_lit).
  th_release FRM U.
  subst U. rewrite ?Z_to_bv_bv_unsigned. apply evt_done.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MINV|]. split; assumption.
Qed.

Section CCtrl.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.

(* [comment removed for export] *)
Definition ctrl_info_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len off fl : Z) (iw shw rrw numw padw rmaxw rflw : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 3 -> a3 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0xba3ef0 ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_ctrl m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (len - off)) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m') c).

Theorem ctrl_info_cps : ctrl_info_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len off fl iw shw rrw numw padw rmaxw rflw
    FDO MST -> -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL INR RAL RC ART0 MI0 CALL.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 80 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - LOR; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  unfold readp_cells in RC.
  pose proof (ci_walk ra sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R fl iw shw rrw numw padw _ _ rmaxw rflw
                HLO1 HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO MI0) as W0.
  fold usp in W0.
  cl_lift W0 HA c1 Hc1.
  apply Hk. eapply ASTA_conseq; [exact Hc1|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m1 & -> & MU1 & WM1 & MI1 & ST1).
  fold usp in MU1, ST1. exists m1. split; [do 16 eexists; reflexivity|].
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  split; [exact (conj ART1 (conj MI1 (conj WM1 ST1)))|].
  intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 80 _ ART0 ltac:(lia) ltac:(lia) Hx); lia.
Qed.

(* [comment removed for export] *)

Definition CP_W (BM R D max PP : Z) : list (Z * Z) := [(PP, PP + 8); (BM, BM + 8); (R + 8, R + 16); (D, D + max)].

(* [comment removed for export] *)
Definition ctrl_ptr_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl iw PP : Z) (shw rrw numw padw rmaxw flw oldpp : word) (junk : list byte),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a3 = Z_to_bv 64 PP -> tp = Z_to_bv 64 0xba3ef0 ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) ->
  fl_ok fl -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max flw) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw flw) ->
  In (D, max) (rt_live RT Σ) -> 0 < max < 2 ^ 31 -> 0 <= off <= len -> len <= max ->
  rw_cells asegs m D [CB (Z.to_nat max) junk] -> length junk = Z.to_nat max ->
  D <> BB -> D <> BM -> D <> R -> BM <> R ->
  PP mod 8 = 0 -> rw_cells asegs m PP [C8 oldpp] -> pp_loc (rt_frames RT Σ) m (bv_unsigned sp) PP ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 144 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_ctrl m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists rmaxw' m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m'
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(PP, PP + 8); (BM, BM + 8); (R + 8, R + 16); (D, D + max)] m m'
        /\ rw_cells asegs m' BM (bufmem_cells (len - off) D max flw)
        /\ rw_cells asegs m' R (readp_cells (len - off) D 0 rmaxw' flw)
        /\ rw_cells asegs m' D [CB (Z.to_nat max) (mv_cur (Z.to_nat off) junk (Z.to_nat (len - off)))]
        /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 BM)]) c).

Theorem ctrl_ptr_cps : ctrl_ptr_stmt.
Proof.
  intros Z0 PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl iw PP
    shw rrw numw padw rmaxw flw oldpp junk
    PMFD PMST -> -> -> -> LVBI ALBI CBIO FLGS INIT LVBB ALBB CBB LVBM ALBM CBM LVR ALR CRP LVD MAXB OFFB LENB CDAT LJ NDBB NDBM NDR NMR ALPP CPP PLOC ARTm INVm CALLm STKB.
  intros T c ENTRY KONT.
  pose proof CALLm as (STKm & SPWIN & SPRES & SPTOP & SPAL).
  pose proof (af_sp0_win RT AF Z0 m ARTm) as SP0W. pose proof (af_sp0_range RT AF Z0 m ARTm) as SP0R.
  set (usp := bv_unsigned sp) in *.
  destruct (af_client_consts RT AF Z0 m ARTm) as (_ & SHDW & _ & _ & UNT).
  pose proof (af_live_range RT AF Z0 m BI 128 ARTm LVBI) as (BIpos & BItop & _).
  pose proof (af_live_range RT AF Z0 m BB 16 ARTm LVBB) as (BBpos & BBtop & _).
  pose proof (af_live_range RT AF Z0 m BM 32 ARTm LVBM) as (BMpos & BMtop & _).
  pose proof (af_live_range RT AF Z0 m R 32 ARTm LVR) as (Rpos & Rtop & _).
  pose proof (af_live_range RT AF Z0 m D max ARTm LVD) as (Dpos & Dtop & _).
  pose proof (afp_live_hi RT GOBJ AFP Z0 m BI 128 ARTm LVBI ltac:(lia)) as BIhi.
  pose proof (afp_live_hi RT GOBJ AFP Z0 m BB 16 ARTm LVBB ltac:(lia)) as BBhi.
  pose proof (afp_live_hi RT GOBJ AFP Z0 m BM 32 ARTm LVBM ltac:(lia)) as BMhi.
  pose proof (afp_live_hi RT GOBJ AFP Z0 m R 32 ARTm LVR ltac:(lia)) as Rhi.
  pose proof (proj2 (af_acc_live RT AF Z0 m BI 128 ARTm LVBI)) as BIacc.
  pose proof (proj2 (af_acc_live RT AF Z0 m BB 16 ARTm LVBB)) as BBacc.
  pose proof (proj2 (af_acc_live RT AF Z0 m BM 32 ARTm LVBM)) as BMacc.
  pose proof (proj2 (af_acc_live RT AF Z0 m R 32 ARTm LVR)) as Racc.
  pose proof (proj1 (af_acc_live RT AF Z0 m D max ARTm LVD)) as Dwr.
  pose proof (proj2 (af_acc_live RT AF Z0 m D max ARTm LVD)) as Dacc.
  pose proof (pp_facts RT AF Z0 m usp lo PP ARTm PLOC ALPP SPWIN SPRES SPTOP) as (PPpos & PPtop & PPut & PPsh & PPstk & PPcl & PPap & PPaccF).
  pose proof (PPaccF m ARTm (fun _ _ => eq_refl)) as PPaccm.
  pose proof (live_ne_apart RT AF Z0 m D max BM 32 ARTm LVD LVBM ltac:(intros E; injection E; intros; apply NDBM; assumption)) as DBMap.
  pose proof (live_ne_apart RT AF Z0 m D max R 32 ARTm LVD LVR ltac:(intros E; injection E; intros; apply NDR; assumption)) as DRap.
  pose proof (live_ne_apart RT AF Z0 m BM 32 R 32 ARTm LVBM LVR ltac:(intros E; injection E; intros; apply NMR; assumption)) as MRap.
  pose proof (live_ne_apart RT AF Z0 m D max BB 16 ARTm LVD LVBB ltac:(intros E; injection E; intros; apply NDBB; assumption)) as DBBap.
  pose proof (live_ne_apart RT AF Z0 m BB 16 BM 32 ARTm LVBB LVBM ltac:(intro E; injection E as E1 E2; lia)) as BBMap.
  pose proof (live_ne_apart RT AF Z0 m BB 16 R 32 ARTm LVBB LVR ltac:(intro E; injection E as E1 E2; lia)) as BBRap.
  assert (LOW80 : lo <= usp - 80) by (unfold RT_STACK in *; lia).
  assert (LOW144 : lo <= usp - 144) by (unfold RT_STACK in STKB; lia).
  assert (LOHI : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (USPHI : usp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (USP80 : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  (* walk to the mem_buf_sync call *)
  pose proof (cp_s0_walk ra sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R PP fl (Z_to_bv 64 iw)
                shw rrw numw padw (Z_to_bv 64 (len - off)) (Z_to_bv 64 (D + off)) rmaxw flw LOW80 LOHI USPHI STKm UNT SHDW CBIO FLGS BIacc BIpos ALBI BIhi ltac:(lia)
                CBB BBacc BBpos ALBB BBhi ltac:(lia) BMacc BMpos ALBM BMhi ltac:(lia) CRP Racc Rpos ALR Rhi ltac:(lia) ltac:(lia) INVm) as WALK0.
  fold usp in WALK0. cl_lift WALK0 ENTRY c1 RZ1.
  destruct (ASTA_unpack RT Z0 _ _ c1 RZ1) as (ms1 & (jk & m1 & -> & MU1 & WM1 & INV1 & FRM1 & STK1) & AT1). clear RZ1. fold usp in MU1, FRM1, STK1, AT1.
  assert (SHF1 : sh_fp [(usp - 80, usp)]) by sh_fp_lia. assert (UTF1 : ut_fp [(usp - 80, usp)]) by ut_fp_lia.
  assert (ART1 : ART RT Z0 m1) by exact (cl_seg_ART RT AF Z0 m m1 usp 80 [] ARTm ltac:(unfold STACK_WIN in *; lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1).
  destruct (af_client_consts RT AF Z0 m1 ART1) as (_ & SHADW1 & _ & _ & UNT1).
  assert (CBIO1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)))
    by (eapply rw_cells_transport; [exact CBIO| exact MU1| exact WM1| unfold bio_w1_cells; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  assert (CBB1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]) by (eapply rw_cells_transport; [exact CBB| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  assert (CBM1 : rw_cells asegs m1 BM (bufmem_cells len D max flw)) by (eapply rw_cells_transport; [exact CBM| exact MU1| exact WM1| unfold bufmem_cells; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  assert (CRP1 : rw_cells asegs m1 R (readp_cells len D off rmaxw flw)) by (eapply rw_cells_transport; [exact CRP| exact MU1| exact WM1| unfold readp_cells; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  assert (CPP1 : rw_cells asegs m1 PP [C8 oldpp]) by (eapply rw_cells_transport; [exact CPP| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct PPstk; lia]).
  assert (CDAT1 : rw_cells asegs m1 D [CB (Z.to_nat max) junk]) by (eapply rw_cells_transport; [exact CDAT| exact MU1| exact WM1| cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia]).
  pose proof (acc_munch_sh _ m m1 BI 128 BIacc MU1 SHF1 ltac:(lia) ltac:(lia)) as BIacc1.
  pose proof (acc_munch_sh _ m m1 BB 16 BBacc MU1 SHF1 ltac:(lia) ltac:(lia)) as BBacc1.
  pose proof (acc_munch_sh _ m m1 BM 32 BMacc MU1 SHF1 ltac:(lia) ltac:(lia)) as BMacc1.
  pose proof (acc_munch_sh _ m m1 R 32 Racc MU1 SHF1 ltac:(lia) ltac:(lia)) as Racc1.
  pose proof (acc_munch_sh _ m m1 D max Dacc MU1 SHF1 ltac:(lia) ltac:(lia)) as Dacc1.
  pose proof (acc_munch_sh _ m m1 PP 8 PPaccm MU1 SHF1 ltac:(lia) ltac:(lia)) as PPacc1.
  destruct (Z.eq_dec off 0) as [EO | OFFpos].
  - (* off = 0: read pointer already equals data; mem_buf_sync takes the no-move path *)
    subst off.
    unfold bufmem_cells in CBM1. unfold readp_cells in CRP1.
    replace (len - 0) with len in * by lia. replace (D + 0) with D in * by lia.
    pose proof (sy_same_walk (Z_to_bv 64 SITE_ctrl_sync) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 ((BI + 48) ≫ 3 + 2147450880)) (Z_to_bv 64 len)
                (Z_to_bv 64 ((R + 8) ≫ 3 + 2147450880)) sp a2 (Z_to_bv 64 115) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 (R + 8))
                (Z_to_bv 64 (BM + 8)) (Z_to_bv 64 fl) (Z_to_bv 64 0) (Z_to_bv 64 BB) (Z_to_bv 64 PP) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 1)
                (Z_to_bv 64 BI) (Z_to_bv 64 2147450880) s8 s9 s10 s11 (Z_to_bv 64 (R ≫ 3 + 2147450880)) (Z_to_bv 64 D) (Z_to_bv 64 127) t6 F fc m1
                lo BI 128 BB BM R iw shw rrw numw padw fl (Z_to_bv 64 len) (Z_to_bv 64 D) (Z_to_bv 64 max) flw (Z_to_bv 64 len) rmaxw flw
                ltac:(rewrite USP80; lia) LOHI ltac:(rewrite USP80; lia) ltac:(rewrite USP80; exact STK1) UNT1 SHADW1 CBIO1 INIT BIacc1 ltac:(lia)
                BIpos ALBI BIhi ltac:(lia) CBB1 BBacc1 BBpos ALBB BBhi ltac:(lia) CBM1 BMacc1 BMpos ALBM BMhi ltac:(lia)
                CRP1 Racc1 Rpos ALR Rhi ltac:(lia) INV1) as WALK1.
    cl_lift WALK1 AT1 c2 RZ2.
    destruct (ASTA_unpack RT Z0 _ _ c2 RZ2) as (ms2 & (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & MU2 & WM2 & INV2 & STK2) & AT2).
    clear RZ2. rewrite USP80 in MU2, STK2.
    rewrite (ret_pc_even SITE_ctrl_sync ltac:(unfold SITE_ctrl_sync; lia) eq_refl) in AT2.
    assert (BMrng : 0 <= BM < 2 ^ 64) by (unfold STACK_WIN, USTACK_TOP in *; lia).
    assert (SHF2 : sh_fp [(usp + -80 - 64, usp + -80)]) by sh_fp_lia. assert (UTF2 : ut_fp [(usp + -80 - 64, usp + -80)]) by ut_fp_lia.
    assert (UNT2 : img_untouched m2) by exact (ut_munch _ m1 m2 UNT1 MU2 UTF2).
    assert (FRM2 : rw_cells asegs m2 (usp + -80) (CB 8 jk :: ctrl_frame s7 s6 s5 s4 s3 s2 s1 s0 ra))
      by (eapply rw_cells_transport; [exact FRM1| exact MU2| exact WM2|]; unfold ctrl_frame; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (CBB2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]) by (eapply rw_cells_transport; [exact CBB1| exact MU2| exact WM2|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (CPP2 : rw_cells asegs m2 PP [C8 oldpp]) by (eapply rw_cells_transport; [exact CPP1| exact MU2| exact WM2|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct PPstk; lia).
    assert (CBM2 : rw_cells asegs m2 BM [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C8 flw]) by (eapply rw_cells_transport; [exact CBM1| exact MU2| exact WM2|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (CRP2 : rw_cells asegs m2 R [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 D); C8 rmaxw; C8 flw]) by (eapply rw_cells_transport; [exact CRP1| exact MU2| exact WM2|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (CDAT2 : rw_cells asegs m2 D [CB (Z.to_nat max) junk]) by (eapply rw_cells_transport; [exact CDAT1| exact MU2| exact WM2|]; cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia).
    pose proof (acc_munch_sh _ m1 m2 BB 16 BBacc1 MU2 SHF2 ltac:(lia) ltac:(lia)) as BBacc2.
    pose proof (acc_munch_sh _ m1 m2 PP 8 PPacc1 MU2 SHF2 ltac:(lia) ltac:(lia)) as PPacc2.
    pose proof (cp_s1_walk ra (Z_to_bv 64 SITE_ctrl_sync) sp gp x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6
                  a2 (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI) F fc m2 lo BB BM R PP oldpp jk
                  LOW80 LOHI USPHI STK2 UNT2 FRM2 CBB2 BBacc2 BBpos ALBB BBhi ltac:(lia) BMrng
                  CPP2 PPacc2 ALPP PPpos PPut PPtop PPsh PPstk INV2) as WALK2.
    cl_lift WALK2 AT2 c3 RZ3.
    destruct (ASTA_unpack RT Z0 _ _ c3 RZ3) as (ms3 & (z0 & z1 & z2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m3 & -> & MU3 & WM3 & INV3 & STK3 & PPC3) & AT3). clear RZ3.
    assert (WM12 : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM2).
    assert (WM13 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM12 WM3).
    assert (AG0 : forall a : word, usp <= bv_unsigned a \/ bv_unsigned a < usp - 144 -> outside [(PP, PP + 8)] (bv_unsigned a) -> m3 a = m a).
    { intros a HS HO. rewrite (MU3 a HO).
      rewrite (MU2 a ltac:(cbn [outside]; split; [clear - HS; lia| exact I])).
      exact (MU1 a ltac:(cbn [outside]; split; [clear - HS; lia| exact I])). }
    assert (ART3 : ART RT Z0 m3).
    { apply (af_frame RT AF Z0 m m3 (usp - 144) ARTm ltac:(unfold STACK_WIN in *; lia) ); [| exact WM13].
      intros a NA. apply AG0.
      - destruct (Z_le_gt_dec usp (bv_unsigned a)) as [H|H]; [left; exact H|].
        destruct (Z_lt_ge_dec (bv_unsigned a) (usp - 144)) as [H2|H2]; [right; exact H2|].
        exfalso. apply NA. left. split; [lia| pose proof (bv_unsigned_in_range 64 a); unfold USTACK_TOP in *; lia].
      - cbn [outside]. split; [| exact I]. intros HPP. apply NA.
        replace (bv_unsigned a) with (PP + (bv_unsigned a - PP)) by lia.
        apply (aclient_mono (rt_live RT Z0) (rt_frames RT Z0) usp); [apply PPcl; lia| auto| auto| lia]. }
    apply KONT. eapply ASTA_conseq; [exact AT3|]. intros ms <-.
    exists rmaxw, m3.
    split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [exact ART3| split; [exact INV3| split; [exact WM13| exact STK3]]]|].
    split; [ intros a HA HO; pose proof (cl_split RT AF Z0 m usp 144 (bv_unsigned a) ARTm ltac:(lia) ltac:(lia) HA) as HS; apply AG0; [exact HS| cbn [outside] in HO |- *; split; [exact (proj1 HO)| exact I]] |].
    assert (CBM3 : rw_cells asegs m3 BM [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C8 flw]) by (eapply rw_cells_transport; [exact CBM2| exact MU3| exact WM3|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct (PPap BM 32 LVBM); lia).
    assert (CRP3 : rw_cells asegs m3 R [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 D); C8 rmaxw; C8 flw]) by (eapply rw_cells_transport; [exact CRP2| exact MU3| exact WM3|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct (PPap R 32 LVR); lia).
    assert (CDAT3 : rw_cells asegs m3 D [CB (Z.to_nat max) junk]) by (eapply rw_cells_transport; [exact CDAT2| exact MU3| exact WM3|]; cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; destruct (PPap D max LVD); lia).
    split; [ replace (len - 0) with len by lia; unfold bufmem_cells; exact CBM3 |].
    split; [ unfold readp_cells; replace (len - 0) with len by lia; replace (D + 0) with D by lia; exact CRP3 |].
    split; [ unfold mv_cur; change (Z.to_nat 0) with 0%nat; cbn [skipn]; rewrite firstn_skipn; exact CDAT3 |].
    exact PPC3.
  -     (* off > 0: read pointer behind data; mem_buf_sync memmoves the unread bytes to the front *)
    assert (OFFlo : 0 < off <= len) by lia.
    pose proof (sy_s0a_walk (Z_to_bv 64 SITE_ctrl_sync) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 ((BI + 48) ≫ 3 + 2147450880)) (Z_to_bv 64 (len - off))
                (Z_to_bv 64 ((R + 8) ≫ 3 + 2147450880)) sp a2 (Z_to_bv 64 115) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 (R + 8))
                (Z_to_bv 64 (BM + 8)) (Z_to_bv 64 fl) (Z_to_bv 64 0) (Z_to_bv 64 BB) (Z_to_bv 64 PP) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 1)
                (Z_to_bv 64 BI) (Z_to_bv 64 2147450880) s8 s9 s10 s11 (Z_to_bv 64 (R ≫ 3 + 2147450880)) (Z_to_bv 64 (D + off)) (Z_to_bv 64 127) t6 F fc m1
                lo BI 128 BB BM R D len max off iw shw rrw numw padw fl rmaxw flw
                ltac:(rewrite USP80; lia) LOHI ltac:(rewrite USP80; lia) ltac:(rewrite USP80; exact STK1) UNT1 SHADW1 CBIO1 INIT BIacc1 ltac:(lia)
                BIpos ALBI BIhi ltac:(lia) CBB1 BBacc1 BBpos ALBB BBhi ltac:(lia) CBM1 BMacc1 BMpos ALBM BMhi ltac:(lia)
                CRP1 Racc1 Rpos ALR Rhi ltac:(lia) Dpos ltac:(unfold STACK_WIN, USTACK_TOP in *; lia) OFFlo LENB INV1) as WALK1.
    cl_lift WALK1 AT1 cmm RZmm.
    destruct (ASTA_unpack RT Z0 _ _ cmm RZmm) as (msmm & (q0 & q1 & q2 & jmm & m2a & -> & MUa & WMa & INVa & FRMa & STKa) & ATmm). clear RZmm.
    rewrite USP80 in ATmm, MUa, STKa, FRMa.
    assert (USP144 : bv_unsigned (Z_to_bv 64 (usp + -80 + -64)) = usp + -80 + -64) by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
    assert (ART2a : ART RT Z0 m2a) by exact (cl_seg_ART RT AF Z0 m1 m2a (usp + -80) 64 [] ART1 ltac:(unfold RT_STACK, STACK_WIN in *; lia) ltac:(unfold USTACK_TOP in *; lia) MUa ltac:(intros x Hx; exfalso; apply Hx; exact I) WMa).
    assert (SHFa : sh_fp [(usp + -80 - 64, usp + -80)]) by sh_fp_lia.
    assert (CDAT2a : rw_cells asegs m2a D [CB (Z.to_nat max) junk]) by (eapply rw_cells_transport; [exact CDAT1| exact MUa| exact WMa|]; cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia).
    assert (BYa : bytes_at asegs m2a D junk) by (destruct CDAT2a as [[_ B] _]; cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B).
    assert (WRa : wr_at asegs m2a D max) by (destruct CDAT2a as [[_ _] W]; cbn [cells_size csize] in W; rewrite Nat.add_0_r, Z2Nat.id in W by lia; exact W).
    pose proof (acc_munch_sh _ m1 m2a D max Dacc1 MUa SHFa ltac:(lia) ltac:(lia)) as Dacc2a.
    apply (MMV Z0 PMc (Z_to_bv 64 SITE_sy_memmove) (Z_to_bv 64 (usp + -80 + -64)) gp (Z_to_bv 64 12205808) q0 q1 q2 (Z_to_bv 64 (usp + -80))
             (Z_to_bv 64 BB) (Z_to_bv 64 D) (Z_to_bv 64 (D + off)) (Z_to_bv 64 (len - off)) (Z_to_bv 64 D) (Z_to_bv 64 (R + 8)) (Z_to_bv 64 (BM + 8))
             (Z_to_bv 64 fl) z64 (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 (BB ≫ 3 + 2147450880))
             (Z_to_bv 64 BI) (Z_to_bv 64 2147450880) s8 s9 s10 s11 (Z_to_bv 64 (R ≫ 3 + 2147450880)) (Z_to_bv 64 (D + off)) (Z_to_bv 64 127) t6 F fc
             m2a D off (len - off) junk lo
             PMFD PMST eq_refl eq_refl eq_refl ltac:(unfold STACK_WIN, USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) ltac:(rewrite LJ; rewrite Z2Nat.id by lia; lia) ltac:(rewrite LJ; rewrite Z2Nat.id by lia; unfold STACK_WIN in *; lia)
             BYa
             ltac:(split; [intros _; split; [apply (acc_sub _ _ _ _ _ _ Dacc2a); lia| left; exists D, max; split; [exact LVD| lia]]| left; lia])
             ltac:(rewrite LJ; rewrite Z2Nat.id by lia; split; [intros _; split; [exact Dacc2a| left; exists D, max; split; [exact LVD| lia]]| split; [intros i Hi; apply (acl_live _ _ _ D max); [exact LVD| lia]| exact WRa]])
             ART2a INVa
             ltac:(unfold call_ok; rewrite USP144; split; [exact STKa| split; [unfold STACK_WIN in *; lia| split; [unfold RT_STACK in *; lia| split; [unfold USTACK_TOP in *; lia| apply Z.mod_divide; [lia|]; assert (HM16 : usp mod 16 = 0) by exact SPAL; apply Z.mod_divide in HM16; [|lia]; destruct HM16 as (k16 & Hk16); exists (k16 - 9); lia]]]]) ).
    exact ATmm.
    intros cret AP. unfold icpt_post in AP.
    destruct (ASTA_unpack RT Z0 _ _ cret AP) as (msret & (m2b & RETst & AFTmm & PRESmm & BYmm) & ATret). clear AP.
    destruct AFTmm as (ART2b & INV2b & WM2b & STK2b). rewrite USP144 in STK2b.
    unfold ret_st in RETst.
    destruct RETst as (p0 & p1 & p2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & d3 & d4 & d5 & d6 & Fr & fcr & Eret).
    rewrite (ret_pc_even SITE_sy_memmove ltac:(unfold SITE_sy_memmove; lia) eq_refl) in Eret.
    rewrite Eret in ATret. clear Eret msret.
    destruct (af_client_consts RT AF Z0 m2b ART2b) as (_ & SHADW2b & _ & _ & UNT2b).
    pose proof (proj2 (af_acc_live RT AF Z0 m2b BB 16 ART2b LVBB)) as BBacc2b.
    pose proof (proj2 (af_acc_live RT AF Z0 m2b BM 32 ART2b LVBM)) as BMacc2b.
    pose proof (proj2 (af_acc_live RT AF Z0 m2b R 32 ART2b LVR)) as Racc2b.
    assert (CBB2a : rw_cells asegs m2a BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]) by (eapply rw_cells_transport; [exact CBB1| exact MUa| exact WMa|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (CBM2a : rw_cells asegs m2a BM (bufmem_cells len D max flw)) by (eapply rw_cells_transport; [exact CBM1| exact MUa| exact WMa|]; unfold bufmem_cells; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (CRP2a : rw_cells asegs m2a R (readp_cells len D off rmaxw flw)) by (eapply rw_cells_transport; [exact CRP1| exact MUa| exact WMa|]; unfold readp_cells; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (CBB2b : rw_cells asegs m2b BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
    { eapply rw_cells_agree_nw; [exact CBB2a|]. intros aa Haa. cbn beta in Haa. cbn [cells_size csize Nat.add] in Haa.
       apply PRESmm; [apply (acl_live _ _ _ BB 16); [exact LVBB| lia]| rewrite LJ, Z2Nat.id by lia; destruct DBBap; lia]. }
    assert (CBM2b : rw_cells asegs m2b BM (bufmem_cells len D max flw)).
    { eapply rw_cells_agree_nw; [exact CBM2a|]. intros aa Haa. cbn beta in Haa. unfold bufmem_cells in Haa. cbn [cells_size csize Nat.add] in Haa.
       apply PRESmm; [apply (acl_live _ _ _ BM 32); [exact LVBM| lia]| rewrite LJ, Z2Nat.id by lia; destruct DBMap; lia]. }
    assert (CRP2b : rw_cells asegs m2b R (readp_cells len D off rmaxw flw)).
    { eapply rw_cells_agree_nw; [exact CRP2a|]. intros aa Haa. cbn beta in Haa. unfold readp_cells in Haa. cbn [cells_size csize Nat.add] in Haa.
       apply PRESmm; [apply (acl_live _ _ _ R 32); [exact LVR| lia]| rewrite LJ, Z2Nat.id by lia; destruct DRap; lia]. }
    assert (FRM2b : rw_cells asegs m2b (usp + -80 + -64) (CB 8 jmm :: sy_frame (Z_to_bv 64 1) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 PP) (Z_to_bv 64 BB) a2 sp (Z_to_bv 64 SITE_ctrl_sync))).
    { eapply rw_cells_agree_nw; [exact FRMa|]. intros aa Haa. cbn beta in Haa. unfold sy_frame in Haa. cbn [cells_size csize Nat.add] in Haa.
       apply PRESmm; [apply (acl_stack _ _ (bv_unsigned (Z_to_bv 64 (usp + -80 + -64)))); rewrite USP144; unfold USTACK_TOP in *; lia| rewrite LJ, Z2Nat.id by lia; lia]. }
    pose proof (sy_s1_walk (Z_to_bv 64 SITE_ctrl_sync) (Z_to_bv 64 (usp + -80)) gp p0 p1 p2 sp a2 (Z_to_bv 64 D) b1 b2 b3 b4 b5 b6 b7
                 (Z_to_bv 64 BB) (Z_to_bv 64 PP) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 1) (Z_to_bv 64 BI) (Z_to_bv 64 2147450880)
                 s8 s9 s10 s11 d3 d4 d5 d6 Fr fcr m2b lo BB BM R D len max off rmaxw flw jmm
                 ltac:(rewrite USP80; lia) LOHI ltac:(rewrite USP80; lia) ltac:(rewrite USP80; exact STK2b) UNT2b SHADW2b ltac:(rewrite USP80; exact FRM2b)
                 CBB2b BBacc2b BBpos ALBB BBhi ltac:(lia) CBM2b BMacc2b BMpos ALBM BMhi ltac:(lia) CRP2b Racc2b Rpos ALR Rhi ltac:(lia)
                 ltac:(destruct MRap; lia) Dpos ltac:(unfold STACK_WIN, USTACK_TOP in *; lia) OFFB LENB INV2b) as WALK2.
    rewrite USP80 in WALK2.
    cl_lift WALK2 ATret c4 RZ4.
    destruct (ASTA_unpack RT Z0 _ _ c4 RZ4) as (ms4 & (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & e14 & m2c & -> & MU2c & WM2c & INV2c & STK2c & CBMc & CRPc) & ATsync). clear RZ4.
    rewrite (ret_pc_even SITE_ctrl_sync ltac:(unfold SITE_ctrl_sync; lia) eq_refl) in ATsync.
    assert (WMm2b : wmono asegs m m2b) by exact (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ WM1 WMa) WM2b).
    assert (WMm2c : wmono asegs m m2c) by exact (wmono_trans asegs _ _ _ WMm2b WM2c).
    assert (ART2c : ART RT Z0 m2c).
    { apply (af_frame RT AF Z0 m2b m2c usp ART2b ltac:(unfold STACK_WIN in *; lia)); [| exact WM2c].
      intros a NA. apply MU2c. cbn [outside]. split; [| split; [| exact I]].
      - intro HC. apply NA. apply (acl_live _ _ _ BM 32); [exact LVBM| lia].
      - intro HC. apply NA. apply (acl_live _ _ _ R 32); [exact LVR| lia]. }
    assert (AGsh : forall a : word, in_fframe_shadow (rt_frames RT Z0) (bv_unsigned a) -> m2c a = m a).
    { intros a Hsh. pose proof Hsh as (f & k & Hin & Hf).
      pose proof (af_frames_range RT AF Z0 m f k ARTm Hin) as (Frp & Frhi & _).
      assert (SHUP : bv_unsigned a < 17594333495296).
      { unfold shad, SHB in Hf. assert ((f + fs_size k) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold USTACK_TOP in *; lia). lia. }
      pose proof (af_fshadow_apart RT AF Z0 m f k ARTm Hin) as (SL & _).
      rewrite (MU2c a ltac:(cbn [outside]; split; [clear - SHUP BMhi; lia| split; [clear - SHUP Rhi; lia| exact I]])).
      rewrite (PRESmm a (acl_fshadow _ _ _ f k _ Hin Hf) ltac:(rewrite LJ, Z2Nat.id by lia; destruct (SL D max LVD) as [Hd|Hd]; clear - Hd Hf; unfold shad, SHB in *; lia)).
      rewrite (MUa a ltac:(cbn [outside]; split; [clear - SHUP LOW144 LOHI; lia| exact I])).
      exact (MU1 a ltac:(cbn [outside]; split; [clear - SHUP LOW80 LOHI; lia| exact I])). }
    assert (PPacc2c : acc asegs m2c PP 8) by (apply (PPaccF m2c ART2c); exact AGsh).
    assert (FRM1a : rw_cells asegs m2a (usp + -80) (CB 8 jk :: ctrl_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FRM1| exact MUa| exact WMa|]; unfold ctrl_frame; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (FRM1b : rw_cells asegs m2b (usp + -80) (CB 8 jk :: ctrl_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_agree_nw; [exact FRM1a|]. intros aa Haa. cbn beta in Haa. unfold ctrl_frame in Haa. cbn [cells_size csize Nat.add] in Haa.
      apply PRESmm; [apply (acl_stack _ _ (bv_unsigned (Z_to_bv 64 (usp + -80 + -64)))); rewrite USP144; unfold USTACK_TOP in *; lia| rewrite LJ, Z2Nat.id by lia; lia]. }
    assert (FRM1c : rw_cells asegs m2c (usp + -80) (CB 8 jk :: ctrl_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FRM1b| exact MU2c| exact WM2c|]; unfold ctrl_frame; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold USTACK_TOP, STACK_WIN, RT_STACK in *; lia).
    assert (CBBc : rw_cells asegs m2c BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]) by (eapply rw_cells_transport; [exact CBB2b| exact MU2c| exact WM2c|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct BBMap; destruct BBRap; lia).
    pose proof (proj2 (af_acc_live RT AF Z0 m2c BB 16 ART2c LVBB)) as BBacc2c.
    assert (CPP2a : rw_cells asegs m2a PP [C8 oldpp]) by (eapply rw_cells_transport; [exact CPP1| exact MUa| exact WMa|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct PPstk; lia).
    assert (CPP2b : rw_cells asegs m2b PP [C8 oldpp]).
    { eapply rw_cells_agree_nw; [exact CPP2a|]. intros aa Haa. cbn beta in Haa. cbn [cells_size csize Nat.add] in Haa.
      apply PRESmm; [apply (aclient_mono (rt_live RT Z0) (rt_frames RT Z0) usp); [replace (bv_unsigned aa) with (PP + (bv_unsigned aa - PP)) by lia; apply PPcl; lia| auto| auto| rewrite USP144; lia]| rewrite LJ, Z2Nat.id by lia; destruct (PPap D max LVD); lia]. }
    assert (CPPc : rw_cells asegs m2c PP [C8 oldpp]) by (eapply rw_cells_transport; [exact CPP2b| exact MU2c| exact WM2c|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct (PPap BM 32 LVBM); destruct (PPap R 32 LVR); lia).
    assert (UNT2c : img_untouched m2c) by (destruct (af_client_consts RT AF Z0 m2c ART2c) as (_ & _ & _ & _ & U); exact U).
    assert (BMrng : 0 <= BM < 2 ^ 64) by (unfold STACK_WIN, USTACK_TOP in *; lia).
    rewrite USP80 in STK2c.
    pose proof (cp_s1_walk ra (Z_to_bv 64 SITE_ctrl_sync) sp gp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 e11 e12 e13 e14
                  a2 (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI) Fr fcr m2c lo BB BM R PP oldpp jk
                  LOW80 LOHI USPHI STK2c UNT2c FRM1c CBBc BBacc2c BBpos ALBB BBhi ltac:(lia) BMrng
                  CPPc PPacc2c ALPP PPpos PPut PPtop PPsh PPstk INV2c) as WALK3.
    cl_lift WALK3 ATsync c5 RZ5.
    destruct (ASTA_unpack RT Z0 _ _ c5 RZ5) as (ms5 & (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & m3 & -> & MU3 & WM3 & INV3 & STK3 & PPC3) & AT3). clear RZ5.
    assert (WM13 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WMm2c WM3).
    assert (ART3 : ART RT Z0 m3).
    { apply (af_frame RT AF Z0 m2c m3 usp ART2c ltac:(unfold STACK_WIN in *; lia)); [| exact WM3].
      intros a NA. apply MU3. cbn [outside]. split; [| exact I]. intro HC. apply NA.
      replace (bv_unsigned a) with (PP + (bv_unsigned a - PP)) by lia. apply PPcl; lia. }
    (* agreement m -> m3 on client addresses outside the footprint, for rt_pres_fp *)
    assert (AGf : forall a : word, aclient (rt_live RT Z0) (rt_frames RT Z0) usp (bv_unsigned a) ->
              outside [(PP, PP + 8); (BM, BM + 8); (R + 8, R + 16); (D, D + max)] (bv_unsigned a) -> m3 a = m a).
    { intros a HA HO. cbn [outside] in HO. destruct HO as (HOp & HOb & HOr & HOd & _).
      pose proof (cl_split RT AF Z0 m usp 144 (bv_unsigned a) ARTm ltac:(lia) ltac:(lia) HA) as HS.
      rewrite (MU3 a ltac:(cbn [outside]; split; [exact HOp| exact I])).
      rewrite (MU2c a ltac:(cbn [outside]; split; [exact HOb| split; [exact HOr| exact I]])).
      rewrite (PRESmm a (aclient_mono (rt_live RT Z0) (rt_frames RT Z0) usp (rt_live RT Z0) (rt_frames RT Z0) (bv_unsigned (Z_to_bv 64 (usp + -80 + -64))) (bv_unsigned a) HA (fun e he => he) (fun e he => he) ltac:(rewrite USP144; lia)) ltac:(rewrite LJ, Z2Nat.id by lia; exact HOd)).
      rewrite (MUa a ltac:(cbn [outside]; split; [clear - HS; lia| exact I])).
      exact (MU1 a ltac:(cbn [outside]; split; [clear - HS; lia| exact I])). }
    apply KONT. eapply ASTA_conseq; [exact AT3|]. intros ms <-.
    exists rmaxw, m3.
    split; [unfold ret_st; do 16 eexists; reflexivity|].
    split; [split; [exact ART3| split; [exact INV3| split; [exact WM13| exact STK3]]]|].
    split; [exact AGf|].
    assert (CBMm3 : rw_cells asegs m3 BM (bufmem_cells (len - off) D max flw)) by (eapply rw_cells_transport; [exact CBMc| exact MU3| exact WM3|]; unfold bufmem_cells; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct (PPap BM 32 LVBM); lia).
    assert (CRPm3 : rw_cells asegs m3 R (readp_cells (len - off) D 0 rmaxw flw)) by (eapply rw_cells_transport; [exact CRPc| exact MU3| exact WM3|]; unfold readp_cells; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct (PPap R 32 LVR); lia).
    (* D block: transport the moved bytes to m3 and rebuild the CB cell *)
    assert (BY2c : bytes_at asegs m2c D (mv_cur (Z.to_nat off) junk (Z.to_nat (len - off)))) by (eapply bytes_at_transport; [exact BYmm| exact MU2c|]; rewrite mv_cur_length by (rewrite LJ; lia); rewrite LJ, Z2Nat.id by lia; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct DBMap; destruct DRap; lia).
    assert (BY3 : bytes_at asegs m3 D (mv_cur (Z.to_nat off) junk (Z.to_nat (len - off)))) by (eapply bytes_at_transport; [exact BY2c| exact MU3|]; rewrite mv_cur_length by (rewrite LJ; lia); rewrite LJ, Z2Nat.id by lia; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct (PPap D max LVD); lia).
    pose proof (proj1 (af_acc_live RT AF Z0 m3 D max ART3 LVD)) as WR3.
    split; [exact CBMm3|]. split; [exact CRPm3|].
    split; [ split; [split; [cbn [cells_wf cell_wf]; split; [rewrite mv_cur_length by (rewrite LJ; lia); exact LJ| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BY3]| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact WR3] |].
    exact PPC3.
Qed.

(* [comment removed for export] *)
Definition ctrl_ptr_same_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R fl iw PP : Z) (shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a3 = Z_to_bv 64 PP -> tp = Z_to_bv 64 0xba3ef0 ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) ->
  fl_ok fl -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM [C8 lw; C8 dw; C8 mw; C8 flw] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R [C8 rlw; C8 dw; C8 rmw; C8 rflw] ->
  PP mod 8 = 0 -> rw_cells asegs m PP [C8 oldpp] -> pp_loc (rt_frames RT Σ) m (bv_unsigned sp) PP ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 144 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_ctrl m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m'
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(PP, PP + 8)] m m'
        /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 BM)]) c).

Theorem ctrl_ptr_same_cps : ctrl_ptr_same_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R fl iw PP
    shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp
    PMFD PMST -> -> -> -> LVBI ALBI CBIO FLGS INIT LVBB ALBB CBB LVBM ALBM CBM LVR ALR CRP ALPP CPP PLOC ARTm INVm CALLm STKB.
  intros T c ENTRY KONT.
  pose proof CALLm as (STKm & SPWIN & SPRES & SPTOP & SPAL).
  pose proof (af_sp0_win RT AF Σ m ARTm) as SP0W. pose proof (af_sp0_range RT AF Σ m ARTm) as SP0R.
  set (usp := bv_unsigned sp) in *.
  destruct (af_client_consts RT AF Σ m ARTm) as (_ & SHDW & _ & _ & UNT).
  pose proof (af_live_range RT AF Σ m BI 128 ARTm LVBI) as (BIpos & BItop & _).
  pose proof (af_live_range RT AF Σ m BB 16 ARTm LVBB) as (BBpos & BBtop & _).
  pose proof (af_live_range RT AF Σ m BM 32 ARTm LVBM) as (BMpos & BMtop & _).
  pose proof (af_live_range RT AF Σ m R 32 ARTm LVR) as (Rpos & Rtop & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ARTm LVBI ltac:(lia)) as BIhi.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ARTm LVBB ltac:(lia)) as BBhi.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ARTm LVBM ltac:(lia)) as BMhi.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ARTm LVR ltac:(lia)) as Rhi.
  pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ARTm LVBI)) as BIacc.
  pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ARTm LVBB)) as BBacc.
  pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ARTm LVBM)) as BMacc.
  pose proof (proj2 (af_acc_live RT AF Σ m R 32 ARTm LVR)) as Racc.
  pose proof (pp_facts RT AF Σ m usp lo PP ARTm PLOC ALPP SPWIN SPRES SPTOP) as (PPpos & PPtop & PPut & PPsh & PPstk & PPcl & PPap & PPacc).
  pose proof (PPacc m ARTm (fun _ _ => eq_refl)) as PPaccm. clear PPacc.
  assert (LOW80 : lo <= usp - 80) by (unfold RT_STACK in *; lia).
  assert (LOHI : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (USPHI : usp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (USP80 : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (LOW144 : lo <= usp - 144) by (unfold RT_STACK in STKB; lia).
  (* walk to the call of mem_buf_sync *)
  pose proof (cp_s0_walk ra sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R PP fl (Z_to_bv 64 iw)
                shw rrw numw padw rlw dw rmw rflw LOW80 LOHI USPHI STKm UNT SHDW CBIO FLGS BIacc BIpos ALBI BIhi ltac:(lia)
                CBB BBacc BBpos ALBB BBhi ltac:(lia) BMacc BMpos ALBM BMhi ltac:(lia) CRP Racc Rpos ALR Rhi ltac:(lia) ltac:(lia) INVm) as WALK0.
  fold usp in WALK0. cl_lift WALK0 ENTRY c1 RZ1.
  destruct (ASTA_unpack RT Σ _ _ c1 RZ1) as (ms1 & (jk & m1 & -> & MU1 & WM1 & INV1 & FRM1 & STK1) & AT1). clear RZ1. fold usp in MU1, FRM1, STK1, AT1.
  assert (SHF1 : sh_fp [(usp - 80, usp)]) by sh_fp_lia. assert (UTF1 : ut_fp [(usp - 80, usp)]) by ut_fp_lia.
  assert (UNT1 : img_untouched m1) by exact (ut_munch _ m m1 UNT MU1 UTF1).
  assert (SHDW1 : ro_cells asegs m1 g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)])
    by (eapply ro_cells_transport; [exact SHDW| exact MU1| (unfold bio_w1_cells, ctrl_frame, g_shadow_memory_dynamic_address in *; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)]).
  assert (CBIO1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)))
    by (eapply rw_cells_transport; [exact CBIO| exact MU1| exact WM1| (unfold bio_w1_cells, ctrl_frame, g_shadow_memory_dynamic_address in *; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)]).
  assert (CBB1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]) by (eapply rw_cells_transport; [exact CBB| exact MU1| exact WM1| (unfold bio_w1_cells, ctrl_frame, g_shadow_memory_dynamic_address in *; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)]).
  assert (CBM1 : rw_cells asegs m1 BM [C8 lw; C8 dw; C8 mw; C8 flw]) by (eapply rw_cells_transport; [exact CBM| exact MU1| exact WM1| (unfold bio_w1_cells, ctrl_frame, g_shadow_memory_dynamic_address in *; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)]).
  assert (CRP1 : rw_cells asegs m1 R [C8 rlw; C8 dw; C8 rmw; C8 rflw]) by (eapply rw_cells_transport; [exact CRP| exact MU1| exact WM1| (unfold bio_w1_cells, ctrl_frame, g_shadow_memory_dynamic_address in *; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)]).
  assert (CPP1 : rw_cells asegs m1 PP [C8 oldpp]) by (eapply rw_cells_transport; [exact CPP| exact MU1| exact WM1| (unfold bio_w1_cells, ctrl_frame, g_shadow_memory_dynamic_address in *; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)]).
  pose proof (acc_munch_sh _ m m1 BI 128 BIacc MU1 SHF1 ltac:(lia) ltac:(lia)) as BIacc1.
  pose proof (acc_munch_sh _ m m1 BB 16 BBacc MU1 SHF1 ltac:(lia) ltac:(lia)) as BBacc1.
  pose proof (acc_munch_sh _ m m1 BM 32 BMacc MU1 SHF1 ltac:(lia) ltac:(lia)) as BMacc1.
  pose proof (acc_munch_sh _ m m1 R 32 Racc MU1 SHF1 ltac:(lia) ltac:(lia)) as Racc1.
  pose proof (acc_munch_sh _ m m1 PP 8 PPaccm MU1 SHF1 ltac:(lia) ltac:(lia)) as PPacc1.
  (* mem_buf_sync with equal data pointers *)
  pose proof (sy_same_walk (Z_to_bv 64 SITE_ctrl_sync) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 ((BI + 48) ≫ 3 + 2147450880)) rlw
                (Z_to_bv 64 ((R + 8) ≫ 3 + 2147450880)) sp a2 (Z_to_bv 64 115) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 (R + 8))
                (Z_to_bv 64 (BM + 8)) (Z_to_bv 64 fl) (Z_to_bv 64 0) (Z_to_bv 64 BB) (Z_to_bv 64 PP) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 1)
                (Z_to_bv 64 BI) (Z_to_bv 64 2147450880) s8 s9 s10 s11 (Z_to_bv 64 (R ≫ 3 + 2147450880)) dw (Z_to_bv 64 127) t6 F fc m1
                lo BI 128 BB BM R iw shw rrw numw padw fl lw dw mw flw rlw rmw rflw
                ltac:(rewrite USP80; lia) LOHI ltac:(rewrite USP80; lia) ltac:(rewrite USP80; exact STK1) UNT1 SHDW1 CBIO1 INIT BIacc1 ltac:(lia)
                BIpos ALBI BIhi ltac:(lia) CBB1 BBacc1 BBpos ALBB BBhi ltac:(lia) CBM1 BMacc1 BMpos ALBM BMhi ltac:(lia)
                CRP1 Racc1 Rpos ALR Rhi ltac:(lia) INV1) as WALK1.
  cl_lift WALK1 AT1 c2 RZ2.
  destruct (ASTA_unpack RT Σ _ _ c2 RZ2) as (ms2 & (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & MU2 & WM2 & INV2 & STK2) & AT2).
  clear RZ2. rewrite USP80 in MU2, STK2.
  rewrite (ret_pc_even SITE_ctrl_sync ltac:(unfold SITE_ctrl_sync; lia) eq_refl) in AT2.
  assert (SHF2 : sh_fp [(usp + -80 - 64, usp + -80)]) by sh_fp_lia.
  assert (UTF2 : ut_fp [(usp + -80 - 64, usp + -80)]) by ut_fp_lia.
  assert (UNT2 : img_untouched m2) by exact (ut_munch _ m1 m2 UNT1 MU2 UTF2).
  assert (FRM2 : rw_cells asegs m2 (usp + -80) (CB 8 jk :: ctrl_frame s7 s6 s5 s4 s3 s2 s1 s0 ra))
    by (eapply rw_cells_transport; [exact FRM1| exact MU2| exact WM2|]; unfold ctrl_frame; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  assert (CBB2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)])
    by (eapply rw_cells_transport; [exact CBB1| exact MU2| exact WM2|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  assert (CPP2 : rw_cells asegs m2 PP [C8 oldpp])
    by (eapply rw_cells_transport; [exact CPP1| exact MU2| exact WM2|]; cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; destruct PPstk; lia).
  pose proof (acc_munch_sh _ m1 m2 BB 16 BBacc1 MU2 SHF2 ltac:(lia) ltac:(lia)) as BBacc2.
  pose proof (acc_munch_sh _ m1 m2 PP 8 PPacc1 MU2 SHF2 ltac:(lia) ltac:(lia)) as PPacc2.
  assert (BMrng : 0 <= BM < 2 ^ 64) by (unfold STACK_WIN, USTACK_TOP in *; lia).
  pose proof (cp_s1_walk ra (Z_to_bv 64 SITE_ctrl_sync) sp gp x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6
                a2 (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI) F fc m2 lo BB BM R PP oldpp jk
                LOW80 LOHI USPHI STK2 UNT2 FRM2 CBB2 BBacc2 BBpos ALBB BBhi ltac:(lia) BMrng
                CPP2 PPacc2 ALPP PPpos PPut PPtop PPsh PPstk INV2) as WALK2.
  cl_lift WALK2 AT2 c3 RZ3.
  destruct (ASTA_unpack RT Σ _ _ c3 RZ3) as (ms3 & (z0 & z1 & z2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m3 & -> & MU3 & WM3 & INV3 & STK3 & PPC3) & AT3). clear RZ3.
  assert (WM12 : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM2).
  assert (WM13 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM12 WM3).
  assert (AG3 : forall a : word, usp <= bv_unsigned a \/ bv_unsigned a < usp - 144 -> outside [(PP, PP + 8)] (bv_unsigned a) -> m3 a = m a).
  { intros a HS HO. rewrite (MU3 a HO).
     rewrite (MU2 a ltac:(cbn [outside]; split; [clear - HS; lia| exact I])).
     exact (MU1 a ltac:(cbn [outside]; split; [clear - HS; lia| exact I])). }
  assert (ART3 : ART RT Σ m3).
  { apply (af_frame RT AF Σ m m3 (usp - 144) ARTm ltac:(unfold STACK_WIN in *; lia) ); [| exact WM13].
     intros a NA. apply AG3.
     - destruct (Z_le_gt_dec usp (bv_unsigned a)) as [H|H]; [left; exact H|].
       destruct (Z_lt_ge_dec (bv_unsigned a) (usp - 144)) as [H2|H2]; [right; exact H2|].
       exfalso. apply NA. left. split; [lia| pose proof (bv_unsigned_in_range 64 a); unfold USTACK_TOP in *; lia].
     - cbn [outside]. split; [| exact I]. intros HPP. apply NA.
       replace (bv_unsigned a) with (PP + (bv_unsigned a - PP)) by lia.
       apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp); [apply PPcl; lia| auto| auto| lia]. }
  apply KONT. eapply ASTA_conseq; [exact AT3|]. intros ms <-.
  exists m3.
  split; [unfold ret_st; do 16 eexists; reflexivity|].
  split; [split; [exact ART3| split; [exact INV3| split; [exact WM13| exact STK3]]]|].
  split.
  - intros a HA HO. pose proof (cl_split RT AF Σ m usp 144 (bv_unsigned a) ARTm ltac:(lia) ltac:(lia) HA) as HS. apply AG3; [exact HS| exact HO].
  - exact PPC3.
Qed.
End CCtrl.
