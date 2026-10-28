(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_W1_defs Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition SITE_sy_memmove : Z := 0x304f60.
Definition SY_EXIT : Z := 0x304fd0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sy_frame (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition sy_s0a_post (sp gp tp a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' : word) (BB R D len off lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_sy_memmove) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 BB) (Z_to_bv 64 D) (Z_to_bv 64 (D + off)) (Z_to_bv 64 (len - off))
                 (Z_to_bv 64 D) a4 a5 a6 a7 (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 (BB ≫ 3 + 2147450880))
                 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memmove) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) (CB 8 j :: sy_frame s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma sy_s0a_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI nbi BB BM R D len max off : Z) (iw : Z) (shw rrw numw padw : word) (fl : Z) (rmaxw flw : word),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> 0 < iw < 2^31 ->
  acc asegs m BI nbi -> 72 <= nbi -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + nbi <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  rw_cells asegs m BM (bufmem_cells len D max flw) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  rw_cells asegs m R (readp_cells len D off rmaxw flw) -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  0 < D -> D + max < 2^63 -> 0 < off <= len -> len <= max -> mem_inv asegs m ->
  evt asegs (sy_s0a_post sp gp (Z_to_bv 64 0xba3ef0) a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' BB R D len off lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_buf_sync) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros HLO HLOS SPH ST UT SHC BW HIW ACCBI HN BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO BMC ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO D0 DMAX HOFF HLEN MI.
  unfold e_mem_buf_sync, g_shadow_memory_dynamic_address, bio_w1_cells, bufmem_cells, readp_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 64, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 64, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia). assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  assert (EUBI : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 7 zstep. zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  zstep. zstep. zstep.
  do 4 zstep. zstep. th_if_lit. zstep. rewrite (t_sx32_small iw) by lia. zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 4 zstep. zstep. th_if_lit. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 4 zstep. zstep. th_if_lit.
  zstep.
  do 4 zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sy_s0a_post, SITE_sy_memmove, e_asan_memmove, sy_frame. apply evt_done. do 5 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition sy_same_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma sy_same_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI nbi BB BM R : Z) (iw : Z) (shw rrw numw padw : word) (fl : Z) (lw dw mw flw rlw rmw rflw : word),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> 0 < iw < 2^31 ->
  acc asegs m BI nbi -> 72 <= nbi -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + nbi <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  rw_cells asegs m BM [C8 lw; C8 dw; C8 mw; C8 flw] -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  rw_cells asegs m R [C8 rlw; C8 dw; C8 rmw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  mem_inv asegs m ->
  evt asegs (sy_same_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_buf_sync) fc None m (seg_rom asegs)).
Proof.
  intros until rflw. intros HLO HLOS SPH ST UT SHC BW HIW ACCBI HN BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO BMC ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO MI.
  unfold e_mem_buf_sync, g_shadow_memory_dynamic_address, bio_w1_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 64, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 64, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia). assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  assert (EUBI : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 7 zstep. zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  zstep. zstep. zstep.
  do 4 zstep. zstep. th_if_lit. zstep. rewrite (t_sx32_small iw) by lia. zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 4 zstep. zstep. th_if_lit. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  do 4 zstep. zstep. th_if_lit.
  zstep.
  do 4 zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true by (symmetry; apply Z.eqb_refl); cbv iota end.
  do 7 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sy_same_post. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Definition sy_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (BM R D len max off lo : Z) (rmaxw flw : word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(BM, BM + 8); (R + 8, R + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' BM (bufmem_cells (len - off) D max flw) /\ rw_cells asegs m' R (readp_cells (len - off) D 0 rmaxw flw).

Lemma sy_s1_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BB BM R D len max off : Z) (rmaxw flw : word) (j : list byte),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -64) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -64) (CB 8 j :: sy_frame s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  rw_cells asegs m BM (bufmem_cells len D max flw) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  rw_cells asegs m R (readp_cells len D off rmaxw flw) -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  (BM + 32 <= R \/ R + 32 <= BM) -> 0 < D -> D + max < 2^63 -> 0 <= off <= len -> len <= max -> mem_inv asegs m ->
  evt asegs (sy_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 F fc BM R D len max off lo rmaxw flw m)
    (MS (mkR (Z_to_bv 64 SITE_sy_memmove) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 BB) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_sy_memmove) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT SHC FR BBC ACCBB BB0 BBAL BBHI BBLO BMC ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO APMR D0 DMAX HOFF HLEN MI.
  unfold SITE_sy_memmove, g_shadow_memory_dynamic_address, bufmem_cells, readp_cells, sy_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BM, BM + 8); (R + 8, R + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BM, BM + 8); (R + 8, R + 16)]) by ut_fp_lia. assert (HWS : sh_fp [(BM, BM + 8); (R + 8, R + 16)]) by sh_fp_lia.
  assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia). assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  zstep. zstep. th_if_lit.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstep.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep.
  do 4 zstep. zstep. th_if_lit.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep.
  do 7 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sy_s1_post, bufmem_cells, readp_cells. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  replace (len - off - 0) with (len - off) by lia. replace (D + 0) with D by lia. split; assumption.
Qed.

Lemma mv_cur_length : forall off bs i, (off + i <= length bs)%nat -> length (mv_cur off bs i) = length bs.
Proof. intros off bs i H. unfold mv_cur. rewrite length_app, length_firstn, !length_skipn. lia. Qed.

Section CSy.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.

Definition SY_W (BM R D max : Z) : list (Z * Z) := [(BM, BM + 8); (R + 8, R + 16); (D, D + max)].

(* [comment removed for export] *)
Definition mem_buf_sync_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI nbi BB BM R D len max off fl iw : Z) (shw rrw numw padw rmaxw flw : word) (junk : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI ->
  In (BI, nbi) (rt_live RT Σ) -> 72 <= nbi <= 64512 -> BI mod 16 = 0 ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max flw) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw flw) -> BM <> R ->
  In (D, max) (rt_live RT Σ) -> D <> BB -> D <> BM -> D <> R ->
  0 <= off <= len -> len <= max -> 0 < max < 2 ^ 31 -> length junk = Z.to_nat max -> rw_cells asegs m D [CB (Z.to_nat max) junk] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 64 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_buf_sync m)))
    (ASTA RT Σ PMc (fun ms => exists (v rmaxw' : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m'
        /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (SY_W BM R D max) m m'
        /\ rw_cells asegs m' BM (bufmem_cells (len - off) D max flw) /\ rw_cells asegs m' R (readp_cells (len - off) D 0 rmaxw' flw)
        /\ rw_cells asegs m' D [CB (Z.to_nat max) (mv_cur (Z.to_nat off) junk (Z.to_nat (len - off)))])).

(* [comment removed for export] *)
Definition mem_buf_sync_same_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI nbi BB BM R fl iw : Z) (shw rrw numw padw lw dw mw flw rlw rmw rflw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI ->
  In (BI, nbi) (rt_live RT Σ) -> 72 <= nbi <= 64512 -> BI mod 16 = 0 ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM [C8 lw; C8 dw; C8 mw; C8 flw] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R [C8 rlw; C8 dw; C8 rmw; C8 rflw] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 64 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_buf_sync m)))
    (ASTA RT Σ PMc (fun ms => exists (v : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m')).

Theorem mem_buf_sync_same_cps : mem_buf_sync_same_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI nbi BB BM R fl iw shw rrw numw padw lw dw mw flw rlw rmw rflw
    FDO MST -> -> INBI HNBI BIAL BW HIW INBB BBAL BBC INBM BMAL BMC INR RAL RC ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 64 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 64) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI nbi ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + nbi <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI nbi ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI nbi ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  pose proof (sy_same_walk ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI nbi BB BM R iw shw rrw numw padw fl lw dw mw flw rlw rmw rflw
                HLO1 HLOS SPH ST UT SHC BW HIW ACCBI ltac:(clear - HNBI; lia) BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO BMC ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO MI0) as W0.
  fold usp in W0.
  cl_lift W0 HA c1 Hc1.
  apply Hk. eapply ASTA_conseq; [exact Hc1|]. intros ms (x0 & x1 & x2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & m1 & -> & MU1 & WM1 & MI1 & ST1).
  fold usp in MU1, ST1. exists b0, m1. split; [do 16 eexists; reflexivity|].
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  split; [exact (conj ART1 (conj MI1 (conj WM1 ST1)))|].
  intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 64 _ ART0 ltac:(lia) ltac:(lia) Hx); lia.
Qed.

Theorem mem_buf_sync_cps : mem_buf_sync_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI nbi BB BM R D len max off fl iw shw rrw numw padw rmaxw flw junk
    FDO MST -> -> INBI HNBI BIAL BW HIW INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR IND NDBB NDBM NDR HOFF HLEN HMAX LJ DC ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 64 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -64).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 64) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI nbi ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + nbi <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI nbi ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI nbi ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _). assert (DLO : D + max <= lo) by (clear - DLO' LOW; lia). clear DLO'.
  assert (DMAX : D + max < 2 ^ 63) by (clear - DLO HLO1 SPH; lia).
  pose proof (live_ne_apart RT AF Σ m BM 32 R 32 ART0 INBM INR ltac:(intros E; injection E; exact NMR)) as APMR.
  pose proof (live_ne_apart RT AF Σ m D max BB 16 ART0 IND INBB ltac:(intros E; injection E; intros _; exact NDBB)) as APDBB.
  pose proof (live_ne_apart RT AF Σ m D max BM 32 ART0 IND INBM ltac:(intros E; injection E; intros _; exact NDBM)) as APDBM.
  pose proof (live_ne_apart RT AF Σ m D max R 32 ART0 IND INR ltac:(intros E; injection E; intros _; exact NDR)) as APDR.
  pose proof (proj2 (proj1 DC)) as DB. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB.
  destruct (Z.eq_dec off 0) as [-> | OFFNZ].
  - (* [comment removed for export] *)
    unfold readp_cells in RC. rewrite Z.sub_0_r, Z.add_0_r in RC. unfold bufmem_cells in BMC.
    pose proof (sy_same_walk ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI nbi BB BM R iw shw rrw numw padw fl
                  (Z_to_bv 64 len) (Z_to_bv 64 D) (Z_to_bv 64 max) flw (Z_to_bv 64 len) rmaxw flw
                  HLO1 HLOS SPH ST UT SHC BW HIW ACCBI ltac:(clear - HNBI; lia) BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO BMC ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO MI0) as W0.
    fold usp in W0.
    cl_lift W0 HA c1 Hc1.
    apply Hk. eapply ASTA_conseq; [exact Hc1|]. intros ms (x0 & x1 & x2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & m1 & -> & MU1 & WM1 & MI1 & ST1).
    fold usp in MU1, ST1. exists b0, rmaxw, m1. split; [do 16 eexists; reflexivity|].
    pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
    split; [exact (conj ART1 (conj MI1 (conj WM1 ST1)))|].
    split; [intros x Hx _; apply MU1; cbn [outside]; split; [| exact I]; destruct (cl_split RT AF Σ m usp 64 _ ART0 ltac:(lia) ltac:(lia) Hx); lia|].
    assert (AG : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m m1) by (intros a' n H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
    unfold bufmem_cells, readp_cells. rewrite ?Z.sub_0_r, ?Z.add_0_r.
    split; [apply (rw_cells_agree asegs m m1 _ _ BMC); [apply AG; cbn [cells_size csize Nat.add]; exact BMLO | exact WM1]|].
    split; [apply (rw_cells_agree asegs m m1 _ _ RC); [apply AG; cbn [cells_size csize Nat.add]; exact RLO | exact WM1]|].
    replace (mv_cur (Z.to_nat 0) junk (Z.to_nat len)) with junk by (unfold mv_cur; cbn [skipn Z.to_nat]; symmetry; apply firstn_skipn).
    apply (rw_cells_agree asegs m m1 _ _ DC); [apply AG; cbn [cells_size csize Nat.add]; clear - DLO HMAX; lia | exact WM1].
  - (* [comment removed for export] *)
    pose proof (sy_s0a_walk ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI nbi BB BM R D len max off iw shw rrw numw padw fl rmaxw flw
                  HLO1 HLOS SPH ST UT SHC BW HIW ACCBI ltac:(clear - HNBI; lia) BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO BMC ACCBM BM0 BMAL BMHI BMLO RC ACCR R0 RAL RHI RLO
                  D0 DMAX ltac:(clear - HOFF OFFNZ; lia) HLEN MI0) as W0.
    fold usp in W0. fold usp1 in W0.
    cl_lift W0 HA c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (x0 & x1 & x2 & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
    fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
    pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
    assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x).
    { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 64 _ ART0 ltac:(lia) ltac:(lia) Hx); lia. }
    assert (AG1 : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m m1) by (intros a' n H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
    assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
    { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
      apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 4). lia. }
    assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
    assert (DB1 : bytes_at asegs m1 D junk) by (apply (bytes_at_agree asegs m m1 _ _ DB); apply AG1; rewrite LJ, Z2Nat.id by lia; exact DLO).
    apply (MMV Σ PMc (Z_to_bv 64 SITE_sy_memmove) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 sp (Z_to_bv 64 BB) (Z_to_bv 64 D) (Z_to_bv 64 (D + off)) (Z_to_bv 64 (len - off))
             (Z_to_bv 64 D) a4 a5 a6 a7 (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m1 D off (len - off) junk lo FDO MST eq_refl eq_refl eq_refl ltac:(clear - D0 DLO HLO1 SPH HMAX; lia) ltac:(clear - HOFF; lia) ltac:(clear - HOFF; lia)
             ltac:(rewrite LJ, Z2Nat.id by lia; clear - HLEN; lia) ltac:(rewrite LJ, Z2Nat.id by lia; clear - HMAX; lia) DB1).
    { exact (live_checked_src RT AF Σ m1 _ lo D max (D + off) (len - off) ART1 IND ltac:(clear - HOFF; lia) ltac:(clear - HLEN; lia) LOW). }
    { rewrite LJ, Z2Nat.id by lia. exact (live_checked_dst RT AF Σ m1 _ D max D max ART1 IND ltac:(lia) ltac:(lia) ltac:(lia)). }
    { exact ART1. } { exact MI1. } { exact CO1. }
    { exact Hc1'. }
    clear Hc1'. intros c2 Hc2.
    destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & MV2) & Hc2'). clear Hc2.
    destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
    rewrite EU1 in ST2, PRES2. rewrite LJ, Z2Nat.id in PRES2 by lia. rewrite (ret_pc_even SITE_sy_memmove) in Hc2' by (unfold SITE_sy_memmove; lia).
    assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (D <= bv_unsigned x < D + max) -> m2 x = m x).
    { intros x Hx HnD. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) HnD). exact (P1 x Hx). }
    assert (FR2 : rw_cells asegs m2 usp1 (CB 8 j :: sy_frame s5 s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold sy_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
      apply PRES2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold usp1 in Hx; clear - Hx DLO HLO1; lia]. }
    assert (BBC2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
    { apply (rw_cells_agree asegs m m2 _ _ BBC); [| exact (wmono_trans asegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
      apply P2; [apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia] | clear - Hx APDBB; lia]. }
    assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len D max flw)).
    { apply (rw_cells_agree asegs m m2 _ _ BMC); [| exact (wmono_trans asegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
      apply P2; [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | clear - Hx APDBM; lia]. }
    assert (RC2 : rw_cells asegs m2 R (readp_cells len D off rmaxw flw)).
    { apply (rw_cells_agree asegs m m2 _ _ RC); [| exact (wmono_trans asegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
      apply P2; [apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia] | clear - Hx APDR; lia]. }
    destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2).
    pose proof (proj2 (af_acc_live RT AF Σ m2 BB 16 ART2 INBB)) as ACCBB2. pose proof (proj2 (af_acc_live RT AF Σ m2 BM 32 ART2 INBM)) as ACCBM2.
    pose proof (proj2 (af_acc_live RT AF Σ m2 R 32 ART2 INR)) as ACCR2.
    (* [comment removed for export] *)
    pose proof (sy_s1_walk ra sp gp y0 y1 y2 s0 s1 (Z_to_bv 64 D) h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 lo BB BM R D len max off rmaxw flw j
                  HLO1 HLOS SPH ST2 UT2 SHC2 FR2 BBC2 ACCBB2 BB0 BBAL BBHI BBLO BMC2 ACCBM2 BM0 BMAL BMHI BMLO RC2 ACCR2 R0 RAL RHI RLO APMR D0 DMAX HOFF HLEN MI2) as W1.
    fold usp usp1 in W1.
    cl_lift W1 Hc2' c3 Hc3.
    apply Hk. eapply ASTA_conseq; [exact Hc3|]. intros ms (z0 & z1 & z2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z3 & z4 & z5 & z6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & BMC3 & RC3).
    fold usp in ST3. exists b0, rmaxw, m3. split; [do 16 eexists; reflexivity|].
    assert (ART3 : ART RT Σ m3).
    { apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; lia)); [| exact WM3].
      intros x Hx. apply MU3. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Hx; [apply (acl_live _ _ _ BM 32); [exact INBM|] | apply (acl_live _ _ _ R 32); [exact INR|]]; clear - Hin; lia. }
    split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
    split.
    { intros x Hx Ho. unfold SY_W in Ho. cbn [outside] in Ho. rewrite (MU3 x ltac:(cbn [outside]; clear - Ho; lia)). apply P2; [exact Hx | clear - Ho; lia]. }
    split; [exact BMC3|]. split; [exact RC3|].
    split; [split; [cbn; split; [rewrite mv_cur_length; rewrite LJ; clear - HOFF HLEN; lia | exact I]|]|].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (bytes_at_agree asegs m2 m3 _ _ MV2). intros x Hx. cbv beta in Hx.
      rewrite mv_cur_length in Hx by (rewrite LJ; clear - HOFF HLEN; lia). rewrite LJ, Z2Nat.id in Hx by lia. apply MU3. cbn [outside]. clear - Hx APDBM APDR; lia.
    + cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (proj1 (af_acc_live RT AF Σ m3 D max ART3 IND)).
Qed.
End CSy.
