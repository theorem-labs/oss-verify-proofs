(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_M_malloc Fz_env Fz_M_free Fz_T_sa Fz_W4_kit Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_ukit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Fz_W5_rep Fz_W5_vset Fz_W5_new.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_ERR_set_debug : Z := 0x1fc940.
Definition SITE_dbg_gsi : Z := 0x1fc994.
Definition SITE_dbg_free1 : Z := 0x1fc9e4.
Definition SITE_dbg_strlen1 : Z := 0x1fca08.
Definition SITE_dbg_malloc1 : Z := 0x1fca18.
Definition SITE_dbg_strcpy1 : Z := 0x1fca30.
Definition SITE_dbg_free2 : Z := 0x1fca88.
Definition SITE_dbg_strlen2 : Z := 0x1fcaac.
Definition SITE_dbg_malloc2 : Z := 0x1fcabc.

(* [comment removed for export] *)
Lemma str_head_nz : forall (b : byte) str, ~ In (Z_to_bv 8 0) (b :: str) -> bv_unsigned b <> 0.
Proof.
  intros b str H E. apply H. left. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Definition dbg_s0_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word) (Lf Ln : Z) (line : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_dbg_gsi) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 Ln) (Z_to_bv 64 1) (Z_to_bv 64 6736696)
                 (Z_to_bv 64 Ln) a3 a4 a5 a6 a7 line s3' (Z_to_bv 64 Lf) s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_state) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma dbg_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Lf Ln : Z) (line : word) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (dbg_s0_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5' s7' s8' s9' s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' Lf Ln line lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 Lf) line (Z_to_bv 64 Ln) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_ERR_set_debug) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC MI. unfold e_ERR_set_debug, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 96, SP)]) by ut_fp_lia.
  th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 11 zstep. zstep. replace (SP + -96 + 96) with SP by lia. do 2 zstep. do 3 zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold dbg_s0_post, SITE_dbg_gsi, e_get_state. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition dbg_s1_post (sp gp tp a1 s1 s2 s4 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E top : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR (Z_to_bv 64 SITE_dbg_free1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) a1'
                 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 E) s4 (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + top * 8))
                 (Z_to_bv 64 top) (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m (seg_rom asegs).

Lemma dbg_s1_walk : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (E top bot : Z) (fl mk buf fs ls fn : list word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  es_rep m E top bot fl mk buf fs ls fn -> nth_error fs (Z.to_nat top) = Some (Z_to_bv 64 0) ->
  acc asegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv asegs m ->
  evt asegs (dbg_s1_post sp gp (Z_to_bv 64 0xba3ef0) a1 s1 s2 s4 s10 s11 F fc E top m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_gsi) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 E) a1
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_gsi) fc None m (seg_rom asegs)).
Proof.
  intros until fn. intros HLO HLOS SPH UT ES FS0 ACCE EAL EHI ELO MI. unfold SITE_dbg_gsi in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM. assert (HWS : sh_fp []) by sh_fp_lia.
  zstep. if_cases KE; zify_cond KE. { exfalso. rewrite ?unsigned_lit in KE by lia. lia. }
  zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small top) by lia.
  zstep. rewrite (Z.shiftl_mul_pow2 top 3) by lia. change (2 ^ 3) with 8. zstep. zstep.
  zstep. zstep. zstep. zstep. th_if_lit.
  pose proof (u64arr_read asegs _ (E + 576) fs top (Z_to_bv 64 0) (Z_to_bv 64 (E + top * 8 + 576)) A7 FS0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold dbg_s1_post, SITE_dbg_free1, e_CRYPTO_free. apply evt_done. do 14 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition dbg_s2_post (sp gp tp s1 s2 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (Lf : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR (Z_to_bv 64 SITE_dbg_strlen1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 Lf) a1
                 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 Lf) s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_strlen) fc None m (seg_rom asegs).

Lemma dbg_s2_walk : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (Lf : Z) (b0 : byte) (str slack : list byte),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  bytes_at asegs m Lf (b0 :: str ++ Z_to_bv 8 0 :: slack) -> bv_unsigned b0 <> 0 -> acc asegs m Lf 1 -> 0x10000 <= Lf -> Lf + 1 <= SEGTOP_A -> mem_inv asegs m ->
  evt asegs (dbg_s2_post sp gp (Z_to_bv 64 0xba3ef0) s1 s2 s3 s5 s7 s8 s9 s10 s11 F fc Lf m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_free1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 a0 a1
             a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 Lf) s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_free1) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros HLO HLOS SPH UT SHC SB B0 ACCL LLO LHI MI. unfold SITE_dbg_free1, g_shadow_memory_dynamic_address, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  assert (EUL : bv_unsigned (Z_to_bv 64 Lf) = Lf) by (apply unsigned_lit; lia).
  zstep. if_cases KL; zify_cond KL. { exfalso. lia. }
  chk_pass ACCL Lf 1 0x1fc9f8 10 11.
  pose proof (u8ro_read asegs m Lf (b0 :: str ++ Z_to_bv 8 0 :: slack) 0 b0 (Z_to_bv 64 Lf) SB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. zstep. if_cases KB; zify_cond KB. { exfalso. exact (B0 KB). }
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold dbg_s2_post, SITE_dbg_strlen1, e_strlen. apply evt_done. do 14 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition dbg_s3_post (sp gp tp s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (len : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR (Z_to_bv 64 SITE_dbg_malloc1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_malloc) fc None m (seg_rom asegs).

Lemma dbg_s3_walk : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (len : Z),
  0 <= len < 2^40 -> mem_inv asegs m ->
  evt asegs (dbg_s3_post sp gp (Z_to_bv 64 0xba3ef0) s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 F fc len m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_strlen1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 len) a1
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_strlen1) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros HL MI. unfold SITE_dbg_strlen1 in *.
  do 4 zstep.
  unfold dbg_s3_post, SITE_dbg_malloc1, e_CRYPTO_malloc. apply evt_done. do 12 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition dbg_s4_post (sp gp tp s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E top q : Z) (fl mk buf fs ls fn : list word) (bot : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_dbg_strcpy1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 q) s4
                 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_strcpy) fc None m' (seg_rom asegs)
    /\ munch [(E + top * 8 + 576, E + top * 8 + 584)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ es_rep m' E top bot fl mk buf (upd fs (Z.to_nat top) (Z_to_bv 64 q)) ls fn.

Lemma dbg_s4_walk : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s4 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (E top bot q n : Z) (fl mk buf fs ls fn : list word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 < q -> q + n <= lo -> 0 < n ->
  acc asegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv asegs m ->
  evt asegs (dbg_s4_post sp gp (Z_to_bv 64 0xba3ef0) s1 s2 (Z_to_bv 64 E) s4 (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 top)
               (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 F fc E top q fl mk buf fs ls fn bot m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_malloc1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 q) a1
             a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 E) s4 (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + top * 8))
             (Z_to_bv 64 top) (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_malloc1) fc None m (seg_rom asegs)).
Proof.
  intros until fn. intros HLO HLOS SPH UT ES Q0 QLO N0 ACCE EAL EHI ELO MI. unfold SITE_dbg_malloc1 in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(E + top * 8 + 576, E + top * 8 + 584)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(E + top * 8 + 576, E + top * 8 + 584)]) by ut_fp_lia. assert (HWS : sh_fp [(E + top * 8 + 576, E + top * 8 + 584)]) by sh_fp_lia.
  assert (EUQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zstep. zstep. th_if_lit.
  wstore64 A7 (E + 576) fs top (E + top * 8 + 576).
  zstep. if_cases KQ; zify_cond KQ. { exfalso. lia. }
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold dbg_s4_post, SITE_dbg_strcpy1, e_strcpy. apply evt_done. do 14 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
Definition dbg_s5_post (sp gp tp s1 s4 s5 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E top bot : Z) (fl mk buf fs ls fn : list word) (line : word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_dbg_free2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) a1
                 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + top * 8 + 768)) (Z_to_bv 64 ((E + top * 8 + 768) ≫ 3 + 2147450880)) s4 s5 (Z_to_bv 64 0x7fff8000) s7
                 (Z_to_bv 64 (top * 4)) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom asegs)
    /\ munch [(E + top * 4 + 704, E + top * 4 + 708)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ es_rep m' E top bot fl mk buf fs (upd ls (Z.to_nat top) line) fn.

Lemma dbg_s5_walk : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s4 s5 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (E top bot : Z) (fl mk buf fs ls fn : list word) (line : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  es_rep m E top bot fl mk buf fs ls fn -> nth_error fn (Z.to_nat top) = Some (Z_to_bv 64 0) ->
  acc asegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv asegs m ->
  evt asegs (dbg_s5_post sp gp (Z_to_bv 64 0xba3ef0) s1 s4 s5 (Z_to_bv 64 (E + top * 8)) s9 s10 s11 F fc E top bot fl mk buf fs ls fn line m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_strcpy1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 a0 a1
             a2 a3 a4 a5 a6 a7 line (Z_to_bv 64 E) s4 s5 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 top) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_strcpy1) fc None m (seg_rom asegs)).
Proof.
  intros until line. intros HLO HLOS SPH UT ES FN0 ACCE EAL EHI ELO MI. unfold SITE_dbg_strcpy1 in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(E + top * 4 + 704, E + top * 4 + 708)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(E + top * 4 + 704, E + top * 4 + 708)]) by ut_fp_lia. assert (HWS : sh_fp [(E + top * 4 + 704, E + top * 4 + 708)]) by sh_fp_lia.
  zstep. zstep. rewrite (Z.shiftl_mul_pow2 top 2) by lia. change (2 ^ 2) with 4. zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  wstore32 A8 (E + 704) ls top (E + top * 4 + 704).
  zstep. zstep. zstep. zstep. zstep. th_if_lit.
  pose proof (u64arr_read asegs _ (E + 768) fn top (Z_to_bv 64 0) (Z_to_bv 64 (E + top * 8 + 768)) A9 FN0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold dbg_s5_post, SITE_dbg_free2, e_CRYPTO_free. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
Definition dbg_s6_post (sp gp tp s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (Ln : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR (Z_to_bv 64 SITE_dbg_strlen2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 Ln) a1
                 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_strlen) fc None m (seg_rom asegs).

Lemma dbg_s6_walk : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (Ln : Z) (b0 : byte) (str slack : list byte),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  bytes_at asegs m Ln (b0 :: str ++ Z_to_bv 8 0 :: slack) -> bv_unsigned b0 <> 0 -> acc asegs m Ln 1 -> 0x10000 <= Ln -> Ln + 1 <= SEGTOP_A -> mem_inv asegs m ->
  evt asegs (dbg_s6_post sp gp (Z_to_bv 64 0xba3ef0) (Z_to_bv 64 Ln) s2 s3 s4 s5 s7 s8 s9 s10 s11 F fc Ln m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_free2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 Ln) a0 a1
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_free2) fc None m (seg_rom asegs)).
Proof.
  intros until slack. intros HLO HLOS SPH UT SHC SB B0 ACCL LLO LHI MI. unfold SITE_dbg_free2, g_shadow_memory_dynamic_address, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  assert (EUL : bv_unsigned (Z_to_bv 64 Ln) = Ln) by (apply unsigned_lit; lia).
  zstep. if_cases KL; zify_cond KL. { exfalso. lia. }
  chk_pass ACCL Ln 1 0x1fca9c 10 11.
  pose proof (u8ro_read asegs m Ln (b0 :: str ++ Z_to_bv 8 0 :: slack) 0 b0 (Z_to_bv 64 Ln) SB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. zstep. if_cases KB; zify_cond KB. { exfalso. exact (B0 KB). }
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold dbg_s6_post, SITE_dbg_strlen2, e_strlen. apply evt_done. do 14 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition dbg_s7_post (sp gp tp s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (len : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms = MS (mkR (Z_to_bv 64 SITE_dbg_malloc2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (len + 1)) (Z_to_bv 64 0)
                 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_malloc) fc None m (seg_rom asegs).

Lemma dbg_s7_walk : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (len : Z),
  0 <= len < 2^40 -> mem_inv asegs m ->
  evt asegs (dbg_s7_post sp gp (Z_to_bv 64 0xba3ef0) s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 F fc len m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_strlen2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 len) a1
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_strlen2) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros HL MI. unfold SITE_dbg_strlen2 in *.
  do 4 zstep.
  unfold dbg_s7_post, SITE_dbg_malloc2, e_CRYPTO_malloc. apply evt_done. do 12 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Definition dbg_s8_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E top q Ln lo : Z)
    (fl mk buf fs ls fn : list word) (bot : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 q) (Z_to_bv 64 Ln) a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_strcpy) fc None m' (seg_rom asegs)
    /\ munch [(E + top * 8 + 768, E + top * 8 + 776)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ es_rep m' E top bot fl mk buf fs ls (upd fn (Z.to_nat top) (Z_to_bv 64 q)).

Lemma dbg_s8_walk : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (E top bot q n Ln : Z) (fl mk buf fs ls fn : list word) (j : list byte),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  es_rep m E top bot fl mk buf fs ls fn -> 0 < q -> q + n <= lo -> 0 < n -> 0 <= Ln < 2^64 ->
  acc asegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv asegs m ->
  evt asegs (dbg_s8_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 F fc E top q Ln lo fl mk buf fs ls fn bot m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_malloc2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 Ln) (Z_to_bv 64 q) a1
             a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + top * 8 + 768)) (Z_to_bv 64 ((E + top * 8 + 768) ≫ 3 + 2147450880)) s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_malloc2) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros ST HLO HLOS SPH UT FR ES Q0 QLO N0 HLN ACCE EAL EHI ELO MI. unfold SITE_dbg_malloc2 in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(E + top * 8 + 768, E + top * 8 + 776)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(E + top * 8 + 768, E + top * 8 + 776)]) by ut_fp_lia. assert (HWS : sh_fp [(E + top * 8 + 768, E + top * 8 + 776)]) by sh_fp_lia.
  assert (EUQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zstep. zstep. th_if_lit.
  wstore64 A9 (E + 768) fn top (E + top * 8 + 768).
  zstep. if_cases KQ; zify_cond KQ. { exfalso. lia. }
  zstep. do 11 zstep. zstep. release_frame FR ST SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold dbg_s8_post, e_strcpy. apply evt_done. do 14 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

Section CDbg.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SLC : strlen_icontract RT.
Hypothesis SCPY : strcpy_icontract RT.
Hypothesis C_GSI : get_state_steady_stmt RT.
Hypothesis C_FRN : crypto_free_null_env_stmt RT.
Hypothesis C_CM : crypto_malloc_env_stmt RT.

Definition DBG_SITES : list (Z * Z) :=
  [(SITE_dbg_free1, e_ERR_set_debug); (SITE_dbg_malloc1, e_ERR_set_debug); (SITE_dbg_free2, e_ERR_set_debug); (SITE_dbg_malloc2, e_ERR_set_debug); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition DBG_CALLS : list (Z * Z) :=
  [(SITE_dbg_free1, e_CRYPTO_free); (SITE_dbg_free1, e_free); (SITE_dbg_malloc1, e_CRYPTO_malloc); (SITE_dbg_free2, e_CRYPTO_free); (SITE_dbg_free2, e_free);
   (SITE_dbg_malloc2, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].
Definition DBG_W (E : Z) : list (Z * Z) := [(ERRNO_A, ERRNO_A + 4); (E, E + 904); (G_ALLOW_CUST, G_ALLOW_CUST + 1)].

(* [comment removed for export] *)
Definition lit_ok (L b sz : Z) (str slack : list byte) : Prop :=
  ro_bytes asegs L (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str /\ str <> [] /\ Z.of_nat (length str) + 1 <= 64512
  /\ (- (L + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
  /\ GOBJ b sz /\ b <= L /\ L + Z.of_nat (length str) + 1 <= b + sz /\ 0x10000 <= L /\ L + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= SEGTOP_A.

(* [comment removed for export] *)
Definition err_set_debug_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (od e : word) (k MK SA NODES E LV : Z) (pad tw ne : word) (top bot : Z) (fl mk buf fs ls fn : list word)
    (lb : byte) (canary : word) (Lf bf szf : Z) (strf slf : list byte) (Ln bn szn : Z) (strn sln : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 Lf -> a2 = Z_to_bv 64 Ln ->
  lit_ok Lf bf szf strf slf -> lit_ok Ln bn szn strn sln ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 272 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ERR_set_debug (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) DBG_SITES DBG_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 1 < LIVE_MAX -> 1 <= rt_credit RT Σ ->
  err_env m od e k MK SA NODES E LV pad tw ne -> err_blocks (rt_live RT Σ) MK SA NODES E -> es_rep m E top bot fl mk buf fs ls fn ->
  nth_error fs (Z.to_nat top) = Some (Z_to_bv 64 0) -> nth_error fn (Z.to_nat top) = Some (Z_to_bv 64 0) -> cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ERR_set_debug m)))
    (fun c => exists (Σ' : rts RT) (e' v : word) (qf qn : Z) (ls' : list word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (DBG_W E) m m'
           /\ err_env m' od e' k MK SA NODES E LV pad tw ne
           /\ es_rep m' E top bot fl mk buf (upd fs (Z.to_nat top) (Z_to_bv 64 qf)) ls' (upd fn (Z.to_nat top) (Z_to_bv 64 qn))
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ bytes_at asegs m' qf (strf ++ [Z_to_bv 8 0]) /\ bytes_at asegs m' qn (strn ++ [Z_to_bv 8 0])) c
       /\ rt_live RT Σ' = (qn, Z.of_nat (length strn) + 1) :: (qf, Z.of_nat (length strf) + 1) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < qf /\ 0 < qn /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem err_set_debug_cps : err_set_debug_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer od e k MK SA NODES E LV pad tw ne top bot fl mk buf fs ls fn
    lb canary Lf bf szf strf slf Ln bn szn strn sln FDO MST -> -> -> LITF LITN ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV BLK ES FS0 FN0 CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 272 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -96).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof BLK as (INM & INS & INN & INE & MKAL & SAAL & NAL & EAL).
  pose proof (af_live_range RT AF Σ m MK 72 ART0 INM) as (R1a & R1 & R1c). pose proof (af_live_range RT AF Σ m SA 32 ART0 INS) as (R2a & R2 & R2c).
  pose proof (af_live_range RT AF Σ m NODES 128 ART0 INN) as (R3a & R3 & R3c). pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as (R4a & R4 & _).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia). assert (ELO : E + 904 <= lo) by (clear - R4 LOW; lia).
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 ART0 INE ltac:(lia)) as EHI.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INM INE ltac:(intros X; injection X; lia)) as D1.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INS INE ltac:(intros X; injection X; lia)) as D2.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INN INE ltac:(intros X; injection X; lia)) as D3.
  pose proof ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & HB).
  (* [comment removed for export] *)
  destruct LITF as (ROF & NZF & NEF & LNF & SLF & GOF & BF1 & BF2 & LF0 & LF1). destruct LITN as (RON & NZN & NEN & LNN & SLN & GON & BN1 & BN2 & LN0 & LN1).
  set (nf := Z.of_nat (length strf)) in *. set (nn := Z.of_nat (length strn)) in *.
  destruct strf as [|bf0 strf']; [exact (False_rect _ (NEF eq_refl))|]. destruct strn as [|bn0 strn']; [exact (False_rect _ (NEN eq_refl))|].
  pose proof (str_head_nz _ _ NZF) as BF0. pose proof (str_head_nz _ _ NZN) as BN0.
  assert (Hnf : 1 <= nf) by (unfold nf; cbn [length]; lia). assert (Hnn : 1 <= nn) by (unfold nn; cbn [length]; lia).
  assert (LENF : Z.of_nat (length ((bf0 :: strf') ++ Z_to_bv 8 0 :: slf)) = nf + 1 + Z.of_nat (length slf)) by (rewrite app_length; cbn [length]; unfold nf; cbn [length]; lia).
  assert (LENN : Z.of_nat (length ((bn0 :: strn') ++ Z_to_bv 8 0 :: sln)) = nn + 1 + Z.of_nat (length sln)) by (rewrite app_length; cbn [length]; unfold nn; cbn [length]; lia).
  assert (BYF : forall mm : mem, mem_inv asegs mm -> bytes_at asegs mm Lf ((bf0 :: strf') ++ Z_to_bv 8 0 :: slf)).
  { intros mm MIm. apply ro_bytes_at; [exact MIm | lia | rewrite LENF; unfold SEGTOP_A in *; lia | exact ROF]. }
  assert (BYN : forall mm : mem, mem_inv asegs mm -> bytes_at asegs mm Ln ((bn0 :: strn') ++ Z_to_bv 8 0 :: sln)).
  { intros mm MIm. apply ro_bytes_at; [exact MIm | lia | rewrite LENN; unfold SEGTOP_A in *; lia | exact RON]. }
  assert (CHKF : forall (Σx : rts RT) (mx : mem) (spx : word), ART RT Σx mx -> checked_src RT Σx mx spx lo Lf (nf + 1)).
  { intros Σx mx spx ARTx. split; [intros _; split | left; unfold SEGTOP_A in *; lia].
    - exact (afp_acc_global RT GOBJ AFP Σx mx bf szf Lf (nf + 1) ARTx GOF BF1 ltac:(lia)).
    - right; right; right. unfold SEGTOP_A in *. lia. }
  assert (CHKN : forall (Σx : rts RT) (mx : mem) (spx : word), ART RT Σx mx -> checked_src RT Σx mx spx lo Ln (nn + 1)).
  { intros Σx mx spx ARTx. split; [intros _; split | left; unfold SEGTOP_A in *; lia].
    - exact (afp_acc_global RT GOBJ AFP Σx mx bn szn Ln (nn + 1) ARTx GON BN1 ltac:(lia)).
    - right; right; right. unfold SEGTOP_A in *. lia. }
  (* [comment removed for export] *)
  assert (ENVR : forall a n x, (0xb9f200 <= a /\ a + n <= 0xb9f2e8) \/ (0xb9f500 <= a /\ a + n <= 0xb9f528) \/ (0xbc52a0 <= a /\ a + n <= 0xbc5698)
               \/ (ERRNO_A <= a /\ a + n <= ERRNO_A + 4) \/ (MK <= a /\ a + n <= MK + 72) \/ (SA <= a /\ a + n <= SA + 32) \/ (NODES <= a /\ a + n <= NODES + 128) ->
               a <= x < a + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x /\ ~ (E <= x < E + 904) /\ x <> G_ALLOW_CUST /\ x < usp - 96).
  { intros a' n x H Hx. unfold G_ALLOW_CUST, ERRNO_A, STACK_WIN, RT_STACK, SEGTOP_A in *.
    destruct H as [H|H]. { split; [right; left; apply client_static_intro; right; left; clear - H Hx; lia | clear - H Hx EHI NUM LOW HSTK; lia]. }
    destruct H as [H|H]. { split; [right; left; apply client_static_intro; right; left; clear - H Hx; lia | clear - H Hx EHI NUM LOW HSTK; lia]. }
    destruct H as [H|H]. { split; [right; left; apply client_static_intro; do 6 right; clear - H Hx; lia | clear - H Hx EHI NUM LOW HSTK; lia]. }
    destruct H as [H|H]. { split; [right; left; apply client_static_intro; right; left; clear - H Hx; lia | clear - H Hx EHI NUM LOW HSTK; lia]. }
    destruct H as [H|H]. { split; [apply (acl_live _ _ _ MK 72); [exact INM | clear - H Hx; lia] | clear - H Hx D1 R1 R1c NUM LOW HSTK; lia]. }
    destruct H as [H|H]. { split; [apply (acl_live _ _ _ SA 32); [exact INS | clear - H Hx; lia] | clear - H Hx D2 R2 R2c NUM LOW HSTK; lia]. }
    split; [apply (acl_live _ _ _ NODES 128); [exact INN | clear - H Hx; lia] | clear - H Hx D3 R3 R3c NUM LOW HSTK; lia]. }
  clear D1 D2 D3 R1c R2c R3c.
  (* [comment removed for export] *)
  pose proof (dbg_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Lf Ln a1 lo
                ST HLO1 HLOS SPH UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (A01 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 96 _ ART0 ltac:(lia) ltac:(lia) Hx); lia. }
  assert (ENV1 : err_env m1 od e k MK SA NODES E LV pad tw ne).
  { pose proof ENV as (IC0 & ER0 & CH0). split; [| split].
    - apply (icstat_agree m m1 od IC0); [| exact WM1]. intros a' n H1 H2 x Hx. cbv beta in Hx. apply A01. exact (proj1 (ENVR a' n _ ltac:(left; split; [exact H1 | exact H2]) Hx)).
    - apply (rw_cells_agree asegs m m1 _ _ ER0); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply A01.
      exact (proj1 (ENVR ERRNO_A 4 _ ltac:(do 3 right; left; lia) Hx)).
    - apply (errchain_agree m m1 _ _ _ _ _ _ _ _ _ CH0); [| exact WM1]. intros a' n H x Hx. cbv beta in Hx. apply A01.
      pose proof CH0 as (_ & _ & HK & _). unfold TSD_MAIN_A in H.
      refine (proj1 (ENVR a' n _ _ Hx)). clear - H HK. lia. }
  pose proof ENV1 as (ICS1 & ERC1 & CH1).
  (* [comment removed for export] *)
  apply (C_GSI Σ PMc (Z_to_bv 64 SITE_dbg_gsi) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 Ln) (Z_to_bv 64 1) (Z_to_bv 64 6736696) (Z_to_bv 64 Ln) a3 a4 a5 a6 a7
           a1 s3 (Z_to_bv 64 Lf) s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo od e k MK SA NODES E LV pad tw ne FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 6. }
  { rewrite EU1. unfold usp1. lia. }
  { exact Hfr. } { exact Hcr. } { exact ICS1. } { exact ERC1. } { exact CH1. }
  { exact INM. } { exact INS. } { exact INN. } { exact INE. } { exact MKAL. } { exact SAAL. } { exact NAL. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σg & e1 & Hc2 & LVg & FRSg & SPg & CRg & CGg).
  destruct (ASTA_unpack RT Σg _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ICS2 & ERC2 & CH2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_dbg_gsi) in Hc2' by (unfold SITE_dbg_gsi; lia).
  assert (A02 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (ERRNO_A <= bv_unsigned x < ERRNO_A + 4) -> m2 x = m x).
  { intros x Hx Ho. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(cbn [outside]; exact (conj Ho I))).
    exact (A01 x Hx). }
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. unfold ERRNO_A. cbn [outside]. unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *. clear - H1 H2 Hx R4 NUM LOW HSTK. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (ES2 : es_rep m2 E top bot fl mk buf fs ls fn).
  { apply (es_rep_agree m m2); [exact ES | | exact (wmono_trans asegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx.
    apply A02; [apply (acl_live _ _ _ E 904); [exact INE | lia] | unfold ERRNO_A; clear - Hx EHI; lia]. }
  assert (CLE2 : cl_env m2 lb canary).
  { apply (cl_env_agree m m2 _ _ CLE). intros x Hx. destruct (cl_cell_off E _ EHI Hx) as [HnE Ho]. cbn [outside] in Ho.
    apply A02; [right; left; exact (cl_cell_static _ Hx) | clear - Ho; tauto]. }
  (* [comment removed for export] *)
  destruct (af_client_consts RT AF Σg m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (INE2 : In (E, 904) (rt_live RT Σg)) by (rewrite LVg; exact INE).
  pose proof (proj2 (af_acc_live RT AF Σg m2 E 904 ART2 INE2)) as ACCE2.
  (* [comment removed for export] *)
  pose proof (dbg_s1_walk sp gp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 Ln) a1 s3 (Z_to_bv 64 Lf) s5 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo E top bot fl mk buf fs ls fn
                HLO1 HLOS SPH UT2 ES2 FS0 ACCE2 EAL EHI ELO MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σg _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & a1x & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & ->) & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2).
  { intros x Hx. cbv beta in Hx. apply A02; [apply acl_stack; exact Hx | unfold ERRNO_A, STACK_WIN, RT_STACK in *; clear - Hx NUM LOW HSTK; lia]. }
  assert (FRR2 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m2 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR2). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ERR_set_debug e_CRYPTO_free SITE_dbg_free1 m m2 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG02 FRR2 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX2 & UWC2).
  rewrite <- CGg in CTX2.
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 6). lia. }
  assert (CO2 : call_ok RT Σg m2 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SPg; exact (conj ST2 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (C_FRN Σg PMc (Z_to_bv 64 SITE_dbg_free1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 Ln) (Z_to_bv 64 0) a1x d2 d3 d4 d5 d6 d7
           a1 (Z_to_bv 64 E) (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 top)
           (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 v3 v4 v5 v6 F2 fc2 m2 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ART2 MI2 CO2).
  { rewrite (unsigned_lit SITE_dbg_free1) by (unfold SITE_dbg_free1; lia). exact CTX2. }
  { exact UWC2. }
  { rewrite CGg. apply (proj2 CGH). right; left; reflexivity. }
  { exact CLE2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (vf1 & Hc4).
  destruct (ASTA_unpack RT Σg _ _ c4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & CLE3) & Hc4'). clear Hc4.
  destruct RS3 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite (ret_pc_even SITE_dbg_free1) in Hc4' by (unfold SITE_dbg_free1; lia).
  (* [comment removed for export] *)
  assert (B3 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m3 x = m2 x).
  { intros x Hx HnE HnL. apply PRES3. rewrite LVg, FRSg. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]. }
  destruct (af_client_consts RT AF Σg m3 ART3) as (_ & SHC3 & _ & _ & UT3).
  pose proof (afp_acc_global RT GOBJ AFP Σg m3 bf szf Lf 1 ART3 GOF BF1 ltac:(lia)) as ACCL3.
  (* [comment removed for export] *)
  pose proof (dbg_s2_walk sp gp w0 w1 w2 vf1 g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 Ln) a1 (Z_to_bv 64 E) (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 top)
                (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 w3 w4 w5 w6 F3 fc3 m3 lo Lf bf0 strf' slf
                HLO1 HLOS SPH UT3 SHC3 (BYF m3 MI3) BF0 ACCL3 LF0 ltac:(lia) MI3) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σg _ _ c5 Hc5) as (ms5 & (x0 & x1 & x2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & x3 & x4 & x5 & x6 & ->) & Hc5'). clear Hc5.
  assert (CO3 : call_ok RT Σg m3 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SPg; exact (conj ST3 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (SLC Σg PMc (Z_to_bv 64 SITE_dbg_strlen1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 sp (Z_to_bv 64 Ln) (Z_to_bv 64 Lf) h1 h2 h3 h4 h5 h6 h7
           a1 (Z_to_bv 64 E) (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 top)
           (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 x3 x4 x5 x6 F3 fc3 m3 Lf (bf0 :: strf') slf lo FDO MST eq_refl (BYF m3 MI3) NZF
           ltac:(fold nf; lia) SLF ltac:(unfold SEGTOP_A in *; lia) ltac:(left; fold nf; unfold SEGTOP_A in *; lia) ltac:(fold nf; exact (CHKF Σg m3 _ ART3)) ART3 MI3 CO3).
  { exact Hc5'. }
  clear Hc5'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σg _ _ c6 Hc6) as (ms6 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & _) & Hc6'). clear Hc6.
  destruct RS4 as (y0 & y1 & y2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & y3 & y4 & y5 & y6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_dbg_strlen1) in Hc6' by (unfold SITE_dbg_strlen1; lia). fold nf in Hc6'.
  assert (B4 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m4 x = m2 x).
  { intros x Hx HnE HnL. rewrite (PRES4 x ltac:(rewrite LVg, FRSg; apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(lia)). exact (B3 x Hx HnE HnL). }
  (* [comment removed for export] *)
  pose proof (dbg_s3_walk sp gp y0 y1 y2 i1 i2 i3 i4 i5 i6 i7 (Z_to_bv 64 Ln) a1 (Z_to_bv 64 E) (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 top)
                (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 y3 y4 y5 y6 F4 fc4 m4 nf ltac:(lia) MI4) as W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σg _ _ c7 Hc7) as (ms7 & (z0 & z1 & z2 & k3 & k4 & k5 & k6 & k7 & z3 & z4 & z5 & z6 & ->) & Hc7'). clear Hc7.
  assert (AG24 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m2 m4).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. rewrite (PRES4 x ltac:(left; lia) ltac:(lia)). apply PRES3. left. lia. }
  pose proof (wmono_trans asegs _ _ _ WM3 WM4) as WM24. cl_keep FR2 AG24 WM24 FR4.
  assert (AG04 : agree_on (fun x => usp <= x < USTACK_TOP) m m4).
  { intros x Hx. cbv beta in Hx. rewrite (B4 x ltac:(apply acl_stack; exact Hx) ltac:(unfold STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK; lia)
      ltac:(unfold G_ALLOW_CUST, STACK_WIN, RT_STACK in *; clear - Hx NUM LOW HSTK; lia)). exact (AG02 x Hx). }
  assert (FRR4 : rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m4 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR4). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ERR_set_debug e_CRYPTO_malloc SITE_dbg_malloc1 m m4 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; right; left; reflexivity)) UWC AG04 FRR4 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT)
    as (CTX4 & UWC4).
  rewrite <- CGg in CTX4.
  assert (CLE4 : cl_env m4 lb canary) by (apply (cl_env_pres_ex _ _ _ 0 0 m3 m4 lb canary CLE3 PRES4); intros x _; lia).
  assert (CO4 : call_ok RT Σg m4 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SPg; exact (conj ST4 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (C_CM Σg PMc (Z_to_bv 64 SITE_dbg_malloc1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) z0 z1 z2 sp (Z_to_bv 64 Ln) (Z_to_bv 64 (nf + 1)) (Z_to_bv 64 0) (Z_to_bv 64 0)
           k3 k4 k5 k6 k7 a1 (Z_to_bv 64 E) (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 top)
           (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 z3 z4 z5 z6 F4 fc4 m4 (nf + 1) lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl ltac:(lia) ART4 MI4 CO4).
  { rewrite EU1. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_dbg_malloc1) by (unfold SITE_dbg_malloc1; lia). exact CTX4. }
  { exact UWC4. }
  { rewrite CGg. split; intros x Hx; destruct Hx as [<-|[]]; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [DBG_SITES DBG_CALLS In]; [do 4 right; left; reflexivity | do 6 right; left; reflexivity]. }
  { rewrite LVg. lia. } { rewrite CRg. change (mcost (nf + 1)) with (if nf + 1 <=? 64512 then 0 else 2 * (nf + 1) + 16384). rewrite (proj2 (Z.leb_le _ _)) by lia. lia. }
  { exact CLE4. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ1 & qf & Hc8 & LV1 & FRS1 & SP1 & CR1 & QF0 & QF16 & QFU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c8 Hc8) as (ms8 & (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & CLE5 & WRF5 & ACCF5) & Hc8'). clear Hc8.
  destruct RS5 as (p0 & p1 & p2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & p3 & p4 & p5 & p6 & F5 & fc5 & ->).
  rewrite EU1 in ST5, PRES5. rewrite (ret_pc_even SITE_dbg_malloc1) in Hc8' by (unfold SITE_dbg_malloc1; lia).
  assert (INF1 : In (qf, nf + 1) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INE1 : In (E, 904) (rt_live RT Σ1)) by (rewrite LV1; right; exact INE2).
  pose proof (af_live_range RT AF Σ1 m5 qf (nf + 1) ART5 INF1) as (_ & QFLO & QFI). rewrite SP1, SPg in QFLO.
  assert (B5 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m5 x = m2 x).
  { intros x Hx HnE HnL. rewrite (PRES5 x ltac:(rewrite LVg, FRSg; apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(cbn [outside]; split; [clear - HnL; lia | exact I])).
    exact (B4 x Hx HnE HnL). }
  (* [comment removed for export] *)
  assert (NQF : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (qf <= x < qf + (nf + 1))).
  { intros x Hx. apply (newchunk_apart RT AF Σg Σ1 m5 qf (nf + 1) usp x ART5 LV1 FRS1 SP1 ltac:(rewrite SPg; lia) ltac:(lia)).
    rewrite LVg, FRSg. exact Hx. }
  assert (ES5 : es_rep m5 E top bot fl mk buf fs ls fn).
  { apply (es_rep_agree m2 m5 _ _ _ _ _ _ _ _ _ ES2); [| exact (wmono_trans asegs _ _ _ WM24 WM5)]. intros x Hx. cbv beta in Hx.
    assert (HAx : aclient (rt_live RT Σg) (rt_frames RT Σg) usp1 (bv_unsigned x)) by (apply (acl_live _ _ _ E 904); [exact INE2 | lia]).
    rewrite (PRES5 x HAx ltac:(unfold G_ALLOW_CUST; cbn [outside]; clear - Hx EHI; lia)). rewrite (PRES4 x HAx ltac:(lia)). exact (PRES3 x HAx). }
  destruct (af_client_consts RT AF Σ1 m5 ART5) as (_ & SHC5 & _ & _ & UT5).
  pose proof (proj2 (af_acc_live RT AF Σ1 m5 E 904 ART5 INE1)) as ACCE5.
  (* [comment removed for export] *)
  pose proof (dbg_s4_walk sp gp p0 p1 p2 l1 l2 l3 l4 l5 l6 l7 (Z_to_bv 64 Ln) a1 (Z_to_bv 64 Lf) s10 s11 p3 p4 p5 p6 F5 fc5 m5 lo E top bot qf (nf + 1) fl mk buf fs ls fn
                HLO1 HLOS SPH UT5 ES5 QF0 ltac:(lia) ltac:(lia) ACCE5 EAL EHI ELO MI5) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ1 _ _ c9 Hc9) as (ms9 & (q0 & q1 & q2 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & m6 & -> & MU6 & WM6 & MI6 & ES6) & Hc9'). clear Hc9.
  fold usp in Hc9'. fold usp1 in Hc9'.
  assert (ART6 : ART RT Σ1 m6).
  { apply (af_frame RT AF Σ1 m5 m6 usp1 ART5 ltac:(rewrite SP1, SPg; unfold usp1; lia)); [| exact WM6].
    intros x Hx. apply MU6. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE1 | lia]. }
  assert (B6 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m6 x = m2 x).
  { intros x Hx HnE HnL. rewrite (MU6 x ltac:(cbn [outside]; clear - HnE HT; lia)). exact (B5 x Hx HnE HnL). }
  assert (ST6 : stk asegs m6 lo usp1).
  { apply (stk_agree_nw asegs m5 m6 _ _ ST5). intros x Hx. cbv beta in Hx. apply MU6. cbn [outside]. unfold usp1, STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK HT; lia. }
  assert (CO6 : call_ok RT Σ1 m6 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP1, SPg; exact (conj ST6 (conj LOW COP))).
  assert (SBF6 : bytes_at asegs m6 Lf ((bf0 :: strf') ++ Z_to_bv 8 0 :: slf)) by exact (BYF m6 MI6).
  (* [comment removed for export] *)
  apply (SCPY Σ1 PMc (Z_to_bv 64 SITE_dbg_strcpy1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) q0 q1 q2 sp (Z_to_bv 64 Ln) (Z_to_bv 64 qf) (Z_to_bv 64 Lf) r2 r3 r4 r5 r6 r7
           a1 (Z_to_bv 64 E) (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 top)
           (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 q3 q4 q5 q6 F5 fc5 m6 qf Lf (bf0 :: strf') slf lo FDO MST eq_refl eq_refl SBF6 NZF
           ltac:(fold nf; lia) SLF ltac:(unfold SEGTOP_A in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(left; fold nf; unfold SEGTOP_A in *; lia)).
  { fold nf. exact (CHKF Σ1 m6 _ ART6). }
  { fold nf. exact (live_checked_dst RT AF Σ1 m6 _ qf (nf + 1) qf (nf + 1) ART6 INF1 ltac:(lia) ltac:(lia) ltac:(lia)). }
  { fold nf. unfold SEGTOP_A in *. destruct QFI; [left | right]; lia. }
  { exact ART6. } { exact MI6. } { exact CO6. }
  { exact Hc9'. }
  clear Hc9'. intros c10 Hc10.
  destruct (ASTA_unpack RT Σ1 _ _ c10 Hc10) as (ms10 & (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & CPF7) & Hc10'). clear Hc10.
  destruct RS7 as (n0 & n1 & n2 & o1 & o2 & o3 & o4 & o5 & o6 & o7 & n3 & n4 & n5 & n6 & F7 & fc7 & ->).
  rewrite EU1 in ST7, PRES7. fold nf in PRES7. rewrite (ret_pc_even SITE_dbg_strcpy1) in Hc10' by (unfold SITE_dbg_strcpy1; lia).
  assert (B7 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m7 x = m2 x).
  { intros x Hx HnE HnL. rewrite (PRES7 x ltac:(rewrite LV1, FRS1, LVg, FRSg; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e0 He0; right; exact He0 | auto | unfold usp1; lia]) (NQF _ Hx)).
    exact (B6 x Hx HnE HnL). }
  assert (ES7 : es_rep m7 E top bot fl mk buf (upd fs (Z.to_nat top) (Z_to_bv 64 qf)) ls fn).
  { apply (es_rep_agree m6 m7 _ _ _ _ _ _ _ _ _ ES6); [| exact WM7]. intros x Hx. cbv beta in Hx.
    apply PRES7; [apply (acl_live _ _ _ E 904); [exact INE1 | lia] | apply NQF; apply (acl_live _ _ _ E 904); [exact INE | lia]]. }
  destruct (af_client_consts RT AF Σ1 m7 ART7) as (_ & SHC7 & _ & _ & UT7).
  pose proof (proj2 (af_acc_live RT AF Σ1 m7 E 904 ART7 INE1)) as ACCE7.
  (* [comment removed for export] *)
  pose proof (dbg_s5_walk sp gp n0 n1 n2 (Z_to_bv 64 qf) o1 o2 o3 o4 o5 o6 o7 (Z_to_bv 64 Ln) (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576))
                (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 n3 n4 n5 n6 F7 fc7 m7 lo E top bot fl mk buf (upd fs (Z.to_nat top) (Z_to_bv 64 qf)) ls fn a1
                HLO1 HLOS SPH UT7 ES7 FN0 ACCE7 EAL EHI ELO MI7) as W5.
  fold usp usp1 in W5.
  cl_lift W5 Hc10' c11 Hc11.
  destruct (ASTA_unpack RT Σ1 _ _ c11 Hc11) as (ms11 & (pp0 & pp1 & pp2 & ll1 & ll2 & ll3 & ll4 & ll5 & ll6 & ll7 & pp3 & pp4 & pp5 & pp6 & m8 & -> & MU8 & WM8 & MI8 & ES8) & Hc11'). clear Hc11.
  fold usp in Hc11'. fold usp1 in Hc11'.
  assert (ART8 : ART RT Σ1 m8).
  { apply (af_frame RT AF Σ1 m7 m8 usp1 ART7 ltac:(rewrite SP1, SPg; unfold usp1; lia)); [| exact WM8].
    intros x Hx. apply MU8. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE1 | lia]. }
  assert (B8 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m8 x = m2 x).
  { intros x Hx HnE HnL. rewrite (MU8 x ltac:(cbn [outside]; clear - HnE HT; lia)). exact (B7 x Hx HnE HnL). }
  assert (ST8 : stk asegs m8 lo usp1).
  { apply (stk_agree_nw asegs m7 m8 _ _ ST7). intros x Hx. cbv beta in Hx. apply MU8. cbn [outside]. unfold usp1, STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK HT; lia. }
  assert (AG28 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m2 m8).
  { intros a' n H1 H2 x Hx. cbv beta in Hx.
    assert (HAx : forall live frames, aclient live frames usp1 (bv_unsigned x)) by (intros; left; clear - H1 H2 Hx; lia).
    rewrite (MU8 x ltac:(cbn [outside]; unfold usp1, STACK_WIN, RT_STACK in *; clear - H1 Hx R4 NUM LOW HSTK HT; lia)).
    rewrite (PRES7 x (HAx _ _) ltac:(unfold usp1, STACK_WIN, RT_STACK in *; clear - H1 Hx QFLO NUM LOW HSTK; lia)).
    rewrite (MU6 x ltac:(cbn [outside]; unfold usp1, STACK_WIN, RT_STACK in *; clear - H1 Hx R4 NUM LOW HSTK HT; lia)).
    rewrite (PRES5 x (HAx _ _) ltac:(unfold G_ALLOW_CUST; cbn [outside]; unfold usp1, STACK_WIN, RT_STACK in *; clear - H1 Hx NUM LOW HSTK; lia)).
    rewrite (PRES4 x (HAx _ _) ltac:(lia)). exact (PRES3 x (HAx _ _)). }
  pose proof (wmono_trans asegs _ _ _ WM24 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 WM8)))) as WM28.
  cl_keep FR2 AG28 WM28 FR8.
  assert (AG08 : agree_on (fun x => usp <= x < USTACK_TOP) m m8).
  { intros x Hx. cbv beta in Hx. rewrite (B8 x ltac:(apply acl_stack; exact Hx) ltac:(unfold STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK; lia)
      ltac:(unfold G_ALLOW_CUST, STACK_WIN, RT_STACK in *; clear - Hx NUM LOW HSTK; lia)). exact (AG02 x Hx). }
  assert (FRR8 : rw_cells asegs m8 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m8 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR8). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ERR_set_debug e_CRYPTO_free SITE_dbg_free2 m m8 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(do 2 right; left; reflexivity)) (proj2 CGH _ ltac:(do 3 right; left; reflexivity)) UWC AG08 FRR8 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT)
    as (CTX8 & UWC8).
  rewrite <- CGg, <- CG1 in CTX8.
  (* [comment removed for export] *)
  assert (CLQF : forall x, cl_cell x -> ~ (qf <= x < qf + (nf + 1))) by (intros x Hx; apply NQF; right; left; exact (cl_cell_static _ Hx)).
  assert (CLE6 : cl_env m6 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m5 m6 _ canary CLE5 MU6); cl_fp_lia).
  assert (CLE7 : cl_env m7 (Z_to_bv 8 1) canary) by (apply (cl_env_pres_ex _ _ _ _ _ m6 m7 _ canary CLE6 PRES7); exact CLQF).
  assert (CLE8 : cl_env m8 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m7 m8 _ canary CLE7 MU8); cl_fp_lia).
  assert (CO8 : call_ok RT Σ1 m8 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP1, SPg; exact (conj ST8 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (C_FRN Σ1 PMc (Z_to_bv 64 SITE_dbg_free2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) pp0 pp1 pp2 sp (Z_to_bv 64 Ln) (Z_to_bv 64 0) ll1 ll2 ll3 ll4 ll5 ll6 ll7
           (Z_to_bv 64 (E + top * 8 + 768)) (Z_to_bv 64 ((E + top * 8 + 768) ≫ 3 + 2147450880)) (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 (top * 4)) (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 pp3 pp4 pp5 pp6 F7 fc7 m8 lo
           (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl ART8 MI8 CO8).
  { rewrite (unsigned_lit SITE_dbg_free2) by (unfold SITE_dbg_free2; lia). exact CTX8. }
  { exact UWC8. }
  { rewrite CG1, CGg. apply (proj2 CGH). do 4 right; left; reflexivity. }
  { exact CLE8. }
  { exact Hc11'. }
  clear Hc11'. intros c12 (vf2 & Hc12).
  destruct (ASTA_unpack RT Σ1 _ _ c12 Hc12) as (ms12 & (m9 & RS9 & (ART9 & MI9 & WM9 & ST9) & PRES9 & CLE9) & Hc12'). clear Hc12.
  destruct RS9 as (w0' & w1' & w2' & g1' & g2' & g3' & g4' & g5' & g6' & g7' & w3' & w4' & w5' & w6' & F9 & fc9 & ->).
  rewrite EU1 in ST9, PRES9. rewrite (ret_pc_even SITE_dbg_free2) in Hc12' by (unfold SITE_dbg_free2; lia).
  assert (B9 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m9 x = m2 x).
  { intros x Hx HnE HnL. rewrite (PRES9 x ltac:(rewrite LV1, FRS1, LVg, FRSg; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e0 He0; right; exact He0 | auto | unfold usp1; lia])).
    exact (B8 x Hx HnE HnL). }
  destruct (af_client_consts RT AF Σ1 m9 ART9) as (_ & SHC9 & _ & _ & UT9).
  pose proof (afp_acc_global RT GOBJ AFP Σ1 m9 bn szn Ln 1 ART9 GON BN1 ltac:(lia)) as ACCL9.
  (* [comment removed for export] *)
  pose proof (dbg_s6_walk sp gp w0' w1' w2' vf2 g1' g2' g3' g4' g5' g6' g7' (Z_to_bv 64 (E + top * 8 + 768)) (Z_to_bv 64 ((E + top * 8 + 768) ≫ 3 + 2147450880)) (Z_to_bv 64 Lf)
                (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 (top * 4)) (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11
                w3' w4' w5' w6' F9 fc9 m9 lo Ln bn0 strn' sln HLO1 HLOS SPH UT9 SHC9 (BYN m9 MI9) BN0 ACCL9 LN0 ltac:(lia) MI9) as W6.
  fold usp usp1 in W6.
  cl_lift W6 Hc12' c13 Hc13.
  destruct (ASTA_unpack RT Σ1 _ _ c13 Hc13) as (ms13 & (x0' & x1' & x2' & h1' & h2' & h3' & h4' & h5' & h6' & h7' & x3' & x4' & x5' & x6' & ->) & Hc13'). clear Hc13.
  assert (CO9 : call_ok RT Σ1 m9 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP1, SPg; exact (conj ST9 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (SLC Σ1 PMc (Z_to_bv 64 SITE_dbg_strlen2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) x0' x1' x2' sp (Z_to_bv 64 Ln) (Z_to_bv 64 Ln) h1' h2' h3' h4' h5' h6' h7'
           (Z_to_bv 64 (E + top * 8 + 768)) (Z_to_bv 64 ((E + top * 8 + 768) ≫ 3 + 2147450880)) (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 (top * 4)) (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 x3' x4' x5' x6' F9 fc9 m9 Ln (bn0 :: strn') sln lo
           FDO MST eq_refl (BYN m9 MI9) NZN ltac:(fold nn; lia) SLN ltac:(unfold SEGTOP_A in *; lia) ltac:(left; fold nn; unfold SEGTOP_A in *; lia)
           ltac:(fold nn; exact (CHKN Σ1 m9 _ ART9)) ART9 MI9 CO9).
  { exact Hc13'. }
  clear Hc13'. intros c14 Hc14.
  destruct (ASTA_unpack RT Σ1 _ _ c14 Hc14) as (ms14 & (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & _) & Hc14'). clear Hc14.
  destruct RS10 as (y0' & y1' & y2' & i1' & i2' & i3' & i4' & i5' & i6' & i7' & y3' & y4' & y5' & y6' & F10 & fc10 & ->).
  rewrite EU1 in ST10, PRES10. rewrite (ret_pc_even SITE_dbg_strlen2) in Hc14' by (unfold SITE_dbg_strlen2; lia). fold nn in Hc14'.
  assert (B10 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m10 x = m2 x).
  { intros x Hx HnE HnL. rewrite (PRES10 x ltac:(rewrite LV1, FRS1, LVg, FRSg; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e0 He0; right; exact He0 | auto | unfold usp1; lia]) ltac:(lia)).
    exact (B9 x Hx HnE HnL). }
  (* [comment removed for export] *)
  pose proof (dbg_s7_walk sp gp y0' y1' y2' i1' i2' i3' i4' i5' i6' i7' (Z_to_bv 64 Ln) (Z_to_bv 64 (E + top * 8 + 768)) (Z_to_bv 64 ((E + top * 8 + 768) ≫ 3 + 2147450880)) (Z_to_bv 64 Lf)
                (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 (top * 4)) (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11
                y3' y4' y5' y6' F10 fc10 m10 nn ltac:(lia) MI10) as W7.
  cl_lift W7 Hc14' c15 Hc15.
  destruct (ASTA_unpack RT Σ1 _ _ c15 Hc15) as (ms15 & (z0' & z1' & z2' & k3' & k4' & k5' & k6' & k7' & z3' & z4' & z5' & z6' & ->) & Hc15'). clear Hc15.
  assert (AG8_10 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m8 m10).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. rewrite (PRES10 x ltac:(left; lia) ltac:(lia)). apply PRES9. left. lia. }
  pose proof (wmono_trans asegs _ _ _ WM9 WM10) as WM8_10. cl_keep FR8 AG8_10 WM8_10 FR10.
  assert (AG0_10 : agree_on (fun x => usp <= x < USTACK_TOP) m m10).
  { intros x Hx. cbv beta in Hx. rewrite (B10 x ltac:(apply acl_stack; exact Hx) ltac:(unfold STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK; lia)
      ltac:(unfold G_ALLOW_CUST, STACK_WIN, RT_STACK in *; clear - Hx NUM LOW HSTK; lia)). exact (AG02 x Hx). }
  assert (FRR10 : rw_cells asegs m10 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip m10 (usp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR10). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ERR_set_debug e_CRYPTO_malloc SITE_dbg_malloc2 m m10 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(do 3 right; left; reflexivity)) (proj2 CGH _ ltac:(do 5 right; left; reflexivity)) UWC AG0_10 FRR10 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT)
    as (CTX10 & UWC10).
  rewrite <- CGg, <- CG1 in CTX10.
  assert (CLE10 : cl_env m10 (Z_to_bv 8 1) canary) by (apply (cl_env_pres_ex _ _ _ 0 0 m9 m10 _ canary CLE9 PRES10); intros x _; lia).
  assert (CO10 : call_ok RT Σ1 m10 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP1, SPg; exact (conj ST10 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (C_CM Σ1 PMc (Z_to_bv 64 SITE_dbg_malloc2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) z0' z1' z2' sp (Z_to_bv 64 Ln) (Z_to_bv 64 (nn + 1)) (Z_to_bv 64 0) (Z_to_bv 64 0)
           k3' k4' k5' k6' k7' (Z_to_bv 64 (E + top * 8 + 768)) (Z_to_bv 64 ((E + top * 8 + 768) ≫ 3 + 2147450880)) (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576))
           (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 (top * 4)) (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 z3' z4' z5' z6' F10 fc10 m10
           (nn + 1) lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl ltac:(lia) ART10 MI10 CO10).
  { rewrite EU1. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_dbg_malloc2) by (unfold SITE_dbg_malloc2; lia). exact CTX10. }
  { exact UWC10. }
  { rewrite CG1, CGg. split; intros x Hx; destruct Hx as [<-|[]]; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [DBG_SITES DBG_CALLS In]; [do 4 right; left; reflexivity | do 6 right; left; reflexivity]. }
  { rewrite LV1, LVg. cbn [length]. lia. } { rewrite CR1, CRg. change (mcost (nn + 1)) with (if nn + 1 <=? 64512 then 0 else 2 * (nn + 1) + 16384). rewrite (proj2 (Z.leb_le _ _)) by lia. unfold mcost. rewrite (proj2 (Z.leb_le _ _)) by lia. lia. }
  { exact CLE10. }
  { exact Hc15'. }
  clear Hc15'. intros c16 (Σ2 & qn & Hc16 & LV2 & FRS2 & SP2 & CR2 & QN0 & QN16 & QNU & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c16 Hc16) as (ms16 & (m11 & RS11 & (ART11 & MI11 & WM11 & ST11) & PRES11 & CLE11 & WRN11 & ACCN11) & Hc16'). clear Hc16.
  destruct RS11 as (p0' & p1' & p2' & l1' & l2' & l3' & l4' & l5' & l6' & l7' & p3' & p4' & p5' & p6' & F11 & fc11 & ->).
  rewrite EU1 in ST11, PRES11. rewrite (ret_pc_even SITE_dbg_malloc2) in Hc16' by (unfold SITE_dbg_malloc2; lia).
  assert (INN2 : In (qn, nn + 1) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INE_2 : In (E, 904) (rt_live RT Σ2)) by (rewrite LV2; right; exact INE1).
  assert (INF_2 : In (qf, nf + 1) (rt_live RT Σ2)) by (rewrite LV2; right; exact INF1).
  pose proof (af_live_range RT AF Σ2 m11 qn (nn + 1) ART11 INN2) as (_ & QNLO & QNI). rewrite SP2, SP1, SPg in QNLO.
  assert (B11 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m11 x = m2 x).
  { intros x Hx HnE HnL. rewrite (PRES11 x ltac:(rewrite LV1, FRS1, LVg, FRSg; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e0 He0; right; exact He0 | auto | unfold usp1; lia])
      ltac:(cbn [outside]; split; [clear - HnL; lia | exact I])). exact (B10 x Hx HnE HnL). }
  assert (NQN : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (qn <= x < qn + (nn + 1))).
  { intros x Hx. apply (newchunk_apart RT AF Σ1 Σ2 m11 qn (nn + 1) usp x ART11 LV2 FRS2 SP2 ltac:(rewrite SP1, SPg; lia) ltac:(lia)).
    rewrite LV1, FRS1, LVg, FRSg. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e0 He0; right; exact He0 | auto | lia]. }
  assert (ES11 : es_rep m11 E top bot fl mk buf (upd fs (Z.to_nat top) (Z_to_bv 64 qf)) (upd ls (Z.to_nat top) a1) fn).
  { apply (es_rep_agree m8 m11 _ _ _ _ _ _ _ _ _ ES8); [| exact (wmono_trans asegs _ _ _ WM8_10 WM11)]. intros x Hx. cbv beta in Hx.
    assert (HAx : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned x)) by (apply (acl_live _ _ _ E 904); [exact INE1 | lia]).
    rewrite (PRES11 x HAx ltac:(unfold G_ALLOW_CUST; cbn [outside]; clear - Hx EHI; lia)). rewrite (PRES10 x HAx ltac:(lia)). exact (PRES9 x HAx). }
  assert (AG8_11 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m8 m11).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. rewrite (PRES11 x ltac:(left; lia) ltac:(unfold G_ALLOW_CUST; cbn [outside]; unfold usp1, STACK_WIN, RT_STACK in *; clear - H1 Hx NUM LOW HSTK; lia)).
    rewrite (PRES10 x ltac:(left; lia) ltac:(lia)). apply PRES9. left. lia. }
  pose proof (wmono_trans asegs _ _ _ WM8_10 WM11) as WM8_11. cl_keep FR8 AG8_11 WM8_11 FR11.
  destruct (af_client_consts RT AF Σ2 m11 ART11) as (_ & _ & _ & _ & UT11).
  pose proof (proj2 (af_acc_live RT AF Σ2 m11 E 904 ART11 INE_2)) as ACCE11.
  (* [comment removed for export] *)
  pose proof (dbg_s8_walk sp gp p0' p1' p2' l1' l2' l3' l4' l5' l6' l7' (Z_to_bv 64 Lf) (Z_to_bv 64 (E + top * 8 + 576)) (Z_to_bv 64 (E + top * 8)) (Z_to_bv 64 (top * 4))
                (Z_to_bv 64 ((E + top * 8 + 576) ≫ 3 + 2147450880)) s10 s11 p3' p4' p5' p6' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 F11 fc11 m11 lo E top bot qn (nn + 1) Ln
                fl mk buf (upd fs (Z.to_nat top) (Z_to_bv 64 qf)) (upd ls (Z.to_nat top) a1) fn j
                ST11 HLO1 HLOS SPH UT11 FR11 ES11 QN0 ltac:(lia) ltac:(lia) ltac:(unfold SEGTOP_A in *; lia) ACCE11 EAL EHI ELO MI11) as W8.
  fold usp usp1 in W8.
  cl_lift W8 Hc16' c17 Hc17.
  destruct (ASTA_unpack RT Σ2 _ _ c17 Hc17) as (ms17 & (q0' & q1' & q2' & r2' & r3' & r4' & r5' & r6' & r7' & q3' & q4' & q5' & q6' & m12 & -> & MU12 & WM12 & MI12 & ST12 & ES12) & Hc17'). clear Hc17.
  fold usp in ST12, Hc17'.
  assert (ART12 : ART RT Σ2 m12).
  { apply (af_frame RT AF Σ2 m11 m12 usp1 ART11 ltac:(rewrite SP2, SP1, SPg; unfold usp1; lia)); [| exact WM12].
    intros x Hx. apply MU12. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE_2 | lia]. }
  assert (B12 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m12 x = m2 x).
  { intros x Hx HnE HnL. rewrite (MU12 x ltac:(cbn [outside]; clear - HnE HT; lia)). exact (B11 x Hx HnE HnL). }
  assert (CO12 : call_ok RT Σ2 m12 sp lo).
  { fold usp in SPA, SPT. unfold call_ok. rewrite SP2, SP1, SPg. fold usp. split; [exact ST12|]. split; [exact LOW|]. split; [clear - HSTK; lia|]. exact (conj SPT SPA). }
  assert (SBN12 : bytes_at asegs m12 Ln ((bn0 :: strn') ++ Z_to_bv 8 0 :: sln)) by exact (BYN m12 MI12).
  (* [comment removed for export] *)
  apply (SCPY Σ2 PMc ra sp gp (Z_to_bv 64 0xba3ef0) q0' q1' q2' s0 s1 (Z_to_bv 64 qn) (Z_to_bv 64 Ln) r2' r3' r4' r5' r6' r7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q3' q4' q5' q6'
           F11 fc11 m12 qn Ln (bn0 :: strn') sln lo FDO MST eq_refl eq_refl SBN12 NZN ltac:(fold nn; lia) SLN ltac:(unfold SEGTOP_A in *; lia) ltac:(unfold USTACK_TOP in *; lia)
           ltac:(left; fold nn; unfold SEGTOP_A in *; lia)).
  { fold nn. exact (CHKN Σ2 m12 _ ART12). }
  { fold nn. exact (live_checked_dst RT AF Σ2 m12 _ qn (nn + 1) qn (nn + 1) ART12 INN2 ltac:(lia) ltac:(lia) ltac:(lia)). }
  { fold nn. unfold SEGTOP_A in *. destruct QNI; [left | right]; lia. }
  { exact ART12. } { exact MI12. } { exact CO12. }
  { exact Hc17'. }
  clear Hc17'. intros c18 Hc18. fold nn in Hc18.
  (* [comment removed for export] *)
  pose proof (af_live_disj RT AF Σ1 m5 qf (nf + 1) E 904 [] (rt_live RT Σg) ART5 LV1 INE2) as DQF.
  pose proof (af_live_disj RT AF Σ2 m11 qn (nn + 1) qf (nf + 1) [] (rt_live RT Σ1) ART11 LV2 INF1) as DQN.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m5 qf (nf + 1) ART5 INF1 ltac:(lia)) as QFHI.
  apply Hk. exists Σ2, e1, (Z_to_bv 64 qn), qf, qn, (upd ls (Z.to_nat top) a1).
  split; [| split; [rewrite LV2, LV1, LVg; reflexivity | split; [rewrite FRS2, FRS1; exact FRSg | split; [rewrite SP2, SP1; exact SPg | split; [| split; [exact QF0 | split; [exact QN0 | rewrite CG2, CG1; exact CGg]]]]]]].
  2: { rewrite CR2, CR1, CRg. unfold mcost. rewrite !(proj2 (Z.leb_le _ _)) by lia. lia. }
  eapply ASTA_conseq; [exact Hc18|]. intros ms (m13 & RS13 & (ART13 & MI13 & WM13 & ST13) & PRES13 & CPN13). exists m13.
  split; [exact RS13|].
  assert (B13 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> bv_unsigned x <> G_ALLOW_CUST -> m13 x = m2 x).
  { intros x Hx HnE HnL. rewrite (PRES13 x ltac:(rewrite LV2, FRS2, LV1, FRS1, LVg, FRSg; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e0 He0; right; right; exact He0 | auto | lia]) (NQN _ Hx)).
    exact (B12 x Hx HnE HnL). }
  split; [exact (conj ART13 (conj MI13 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM28 (wmono_trans asegs _ _ _ WM8_11 (wmono_trans asegs _ _ _ WM12 WM13))))) ST13)))|].
  split.
  { intros x Hx Ho. unfold DBG_W, ERRNO_A, G_ALLOW_CUST in Ho. cbn [outside] in Ho.
    rewrite (B13 x Hx ltac:(clear - Ho; lia) ltac:(unfold G_ALLOW_CUST; clear - Ho; lia)). apply A02; [exact Hx | unfold ERRNO_A; clear - Ho; lia]. }
  split.
  { split; [| split].
    - apply (icstat_agree m2 m13 od ICS2); [| exact (wmono_trans asegs _ _ _ WM28 (wmono_trans asegs _ _ _ WM8_11 (wmono_trans asegs _ _ _ WM12 WM13)))].
      intros a' n H1 H2 x Hx. cbv beta in Hx. destruct (ENVR a' n _ ltac:(left; split; [exact H1 | exact H2]) Hx) as (Q1 & Q2 & Q3 & _). exact (B13 x Q1 Q2 Q3).
    - apply (rw_cells_agree asegs m2 m13 _ _ ERC2); [| exact (wmono_trans asegs _ _ _ WM28 (wmono_trans asegs _ _ _ WM8_11 (wmono_trans asegs _ _ _ WM12 WM13)))].
      intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. destruct (ENVR ERRNO_A 4 _ ltac:(do 3 right; left; lia) Hx) as (Q1 & Q2 & Q3 & _). exact (B13 x Q1 Q2 Q3).
    - apply (errchain_agree m2 m13 _ _ _ _ _ _ _ _ _ CH2); [| exact (wmono_trans asegs _ _ _ WM28 (wmono_trans asegs _ _ _ WM8_11 (wmono_trans asegs _ _ _ WM12 WM13)))].
      intros a' n H x Hx. cbv beta in Hx. pose proof CH2 as (_ & _ & HK & _). unfold TSD_MAIN_A in H.
      destruct (ENVR a' n _ ltac:(clear - H HK; lia) Hx) as (Q1 & Q2 & Q3 & _). exact (B13 x Q1 Q2 Q3). }
  split.
  { apply (es_rep_agree m12 m13 _ _ _ _ _ _ _ _ _ ES12); [| exact WM13]. intros x Hx. cbv beta in Hx.
    apply PRES13; [apply (acl_live _ _ _ E 904); [exact INE_2 | lia] | apply NQN; apply (acl_live _ _ _ E 904); [exact INE | lia]]. }
  split.
  { assert (CLE12 : cl_env m12 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m11 m12 _ canary CLE11 MU12); cl_fp_lia).
    apply (cl_env_pres_ex _ _ _ _ _ m12 m13 _ canary CLE12 PRES13). intros x Hx; apply NQN; right; left; exact (cl_cell_static _ Hx). }
  split; [| exact CPN13].
  apply (bytes_at_agree asegs m7 m13 _ _ CPF7). intros x Hx. cbv beta in Hx.
  replace (Z.of_nat (length ((bf0 :: strf') ++ [Z_to_bv 8 0]))) with (nf + 1) in Hx by (rewrite app_length; unfold nf; cbn [length]; lia).
  assert (HAx : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned x)) by (apply (acl_live _ _ _ qf (nf + 1)); [exact INF1 | clear - Hx; lia]).
  rewrite (PRES13 x ltac:(apply (acl_live _ _ _ qf (nf + 1)); [exact INF_2 | clear - Hx; lia]) ltac:(clear - Hx DQN; lia)).
  rewrite (MU12 x ltac:(cbn [outside]; clear - Hx DQF HT; lia)).
  rewrite (PRES11 x HAx ltac:(unfold G_ALLOW_CUST; cbn [outside]; clear - Hx QFHI; lia)). rewrite (PRES10 x HAx ltac:(lia)). rewrite (PRES9 x HAx). apply MU8. cbn [outside]. clear - Hx DQF HT. lia.
Qed.
End CDbg.
