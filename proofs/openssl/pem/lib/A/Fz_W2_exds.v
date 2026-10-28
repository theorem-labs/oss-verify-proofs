(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_ukit Fz_env Th_mutex Fz_M_free Fz_T_lock Fz_W1_defs Fz_W3_iface Fz_W2_exdl Fz_W2_exd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma nx_s2_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 obj c0 c1 : word)
    (F : bvmap 5 word) fc (m : mem) (cls AD LK f lo pd : Z) (j0 j1 j2 j3 j4 j5 j6 j8 j9 g1 g2 : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 256 <= lo -> (f + 256 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 320 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> cls = 12 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  (* [comment removed for export] *)
  ro_cells asegs m DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] -> 0x10007fff8000 <= LK -> LK mod 16 = 0 -> LK + 40 <= lo ->
  rw_cells asegs m LK (mutex_cells z64 z64) -> ro_cells asegs m (DC_GLOBAL_LOCK / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  ro_cells asegs m DC_IP12 [C8 z64] -> ro_cells asegs m (DC_IP12 / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m AD [C8 c0; C8 c1] -> 0xbc6000 <= AD -> AD mod 8 = 0 -> AD + 16 <= lo -> (AD + 16 <= LK \/ LK + 40 <= AD) -> (AD + 16 <= 0x7fff8000 \/ 0x10007fff8000 <= AD) ->
  ro_cells asegs m (AD / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> ro_cells asegs m ((AD + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (bv_unsigned sp + -192 - pd)
    (nxb_frame pd (CB 8 j0) (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4) (CB 8 j5) (CB 8 j6) (C8 obj) (CB 8 j8) (CB 8 j9) (C8 (Z_to_bv 64 f)) g1 g2
               e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0) ->
  stk asegs m lo (bv_unsigned sp + -192 - pd) -> mem_inv asegs m ->
  evt asegs (nx_s2_post sp gp tp t3 t4 t5 t6 F fc ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 obj cls AD LK f lo pd j0 j1 j2 j3 j4 j8 j9 g1 g2 m)
    (MS (mkR (Z_to_bv 64 SITE_nx_exg) (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
             (Z_to_bv 64 DC_GLOBAL_LOCK) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 AD) (Z_to_bv 64 cls) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 f) s8 s9
             s10 (Z_to_bv 64 (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nx_exg) fc None m (seg_rom asegs)).
Proof.
  intros until g2. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH -> UT SHC GL LKLO LKAL LKL LKC GLS IPC IPS ADC AD0 ADAL ADL ADLK ADSH ADS1 ADS2 FR ST MI.
  unfold SITE_nx_exg in *. unfold nxb_frame in FR.
  unfold DC_GLOBAL_LOCK, DC_IP12, DC_INITED, DC_KEY, DC_ONCE1, DC_RET1, DC_ONCE2, DC_RET2, DC_CTX, e_get_ex_data_global, g_shadow_memory_dynamic_address, SHB in *.
  pose proof T_gal_proof as XL. unfold T_gal_stmt, DC_GLOBAL_LOCK, DC_IP12, DC_CTX, e_get_and_lock, g_shadow_memory_dynamic_address, SHB in XL.
  pose proof T_sknum_null_proof as XN. unfold T_sknum_null_stmt, e_sk_num in XN.
  pose proof T_unlock_proof as XU. unfold T_unlock_stmt in XU.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 320, SP - 104); (AD, AD + 16); (LK + 4, LK + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 320, SP - 104); (AD, AD + 16); (LK + 4, LK + 8)]) by (clear - HLO HLOS SPH AD0 ADL LKLO; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUad : bv_unsigned (Z_to_bv 64 AD) = AD) by (apply unsigned_lit; lia).
  destruct HP as [-> | ->]; cbn [Z.eqb app] in FR.
  1: replace (SP + -192 - 0) with (SP + -192) in * by lia.
  2: replace (SP + -192 - 16) with (SP + -208) in * by lia.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: unfold mutex_cells in *.
  all: zstep; if_false. all: zstep. all: zstep. all: zstep; zstep.
  all: tcall (XL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo LK).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  all: try (eapply ut_munch; [exact UT | eassumption | exact HWU]).
  all: cbv beta delta [mkR].
  all: unfold mutex_cells in *.
  (* [comment removed for export] *)
  all: replace ((12187008 + 112) / 8 + 2147450880) with 2148974270 in IPS by reflexivity; replace (12187008 + 112) with 12187120 in IPC by reflexivity.
  all: replace ((12187008 + 8) / 8 + 2147450880) with 2148974257 in GLS by reflexivity; replace (12187008 + 8) with 12187016 in GL by reflexivity.
  (* [comment removed for export] *)
  all: zstep; if_false.
  all: zstep.
  all: zstep; rewrite (shr3_div AD) by lia; zstep; zstep; zstep; if_false.
  (* [comment removed for export] *)
  all: zstep; lfix.
  all: zstep; zstep; rewrite (shr3_div (AD + 8)) by lia; zstep; zstep; zstep; if_false.
  all: zstep; lfix.
  all: zstep; zstep; zstep; zstep; if_false.
  all: zstep; zstep; zstep.
  all: tcall (XN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  all: cbv beta delta [mkR].
  (* [comment removed for export] *)
  all: zstep; zstep; zstep.
  all: zstep; if_true.
  all: zstep; zstep; zstep; zstep; zstep; if_false. all: zstep; zstep.
  all: tcall (XU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  all: cbv beta delta [mkR].
  (* [comment removed for export] *)
  all: zstep; if_true. all: zstep; if_true.
  all: zstep; zstep.
  all: zstep; if_cases KQ; zify_cond KQ; [exfalso; rewrite ?unsigned_lit in KQ by lia; lia|].
  all: zstep; zstep; zstep; zstep; zstep.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold nx_s2_post, nxb_frame, SITE_nx_free, e_CRYPTO_free, EXD_FILE, DC_IP12, DC_GLOBAL_LOCK, DC_CTX, SHB, mutex_cells; cbn [Z.eqb app].
  all: try replace (bv_unsigned sp + -192 - 0) with (bv_unsigned sp + -192) by lia.
  all: try replace (bv_unsigned sp + -192 - 16) with (bv_unsigned sp + -208) by lia.
  all: replace (12187008 + 112) with 12187120 by reflexivity; replace (12187008 + 8) with 12187016 by reflexivity.
  all: apply evt_done; cbv beta; do 9 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact ADC| assumption].
Qed.
