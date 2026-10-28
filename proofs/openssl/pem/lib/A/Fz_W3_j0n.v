(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall Bytes.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_misc Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_ngets.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz := (Z_to_bv 64) (only parsing).
Definition SITE_jn_new1 : Z := 0x30c298.   (* [comment removed for export] *)
Definition SITE_jn_new2 : Z := 0x30c2a4.   (* [comment removed for export] *)
Definition SITE_jn_pmal : Z := 0x30c2c4.   (* [comment removed for export] *)
Definition SITE_jn_gets : Z := 0x30c2f8.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition jn0_post (sp1 : Z) (gp s0 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (e64 : list byte) (c7 c8 c9 c10 c11 : word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (meth : Z) (m' : mem),
    ms = MS (mkR (wz SITE_jn_new1) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz meth) a1 a2 a3 a4 a5 a6 a7 s2 (wz meth) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz FZ_BIO_NEW) fc None m' (seg_rom asegs)
    /\ (meth = M_MEM \/ meth = M_SECMEM)
    /\ munch [(sp1 - 16, sp1); (sp1 + 112, sp1 + 216)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sp1
    /\ rw_cells asegs m' (sp1 + 112) [CB 64 e64; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11].
Lemma jn0_walk : forall ra sp1 gp t0 t1 t2 s0 a0 a1 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (fl lo : Z) (ee : list byte)
    (c7 c8 c9 c10 c11 : word),
  0x10007fff8000 <= lo -> lo + 16 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 <= fl < 256 -> mem_inv asegs m -> stk asegs m lo sp1 ->
  rw_cells asegs m (sp1 + 112) [CB 104 ee] ->
  evt asegs (jn0_post sp1 gp s0 s2 (wz fl) s5 s6 s7 s8 s9 s10 s11 F fc lo (firstn 64 ee) c7 c8 c9 c10 c11 m)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) a0 a1 c10 c11 c8 c7 a6 a7 s2 c9 (wz fl) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_J0N) fc None m (seg_rom asegs)).
Proof.
  intros until c11. intros HLOS HLO SPH FL MI ST FRE. unfold J_J0N, TP_A in *.
  pose proof (munch_refl [(sp1 - 16, sp1); (sp1 + 112, sp1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  zstep. if_cases KS; zify_cond KS.
  - (* [comment removed for export] *)
    zstep.
    tcall (bio_s_secmem_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); [clear - HLO; lia| exact HLOS| clear - SPH; lia| exact ST| exact MI|].
    cbv beta delta [mkR].
    zstep. zstep.
  unfold jn0_post, SITE_jn_new1, FZ_BIO_NEW, M_MEM, M_SECMEM, M_MEM_A, M_SECMEM_A, SECMEM_METHOD. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [right; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption| rewrite !firstn_firstn in FRE; exact FRE].
- zstep.
  tcall (bio_s_mem_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); [clear - HLO; lia| exact HLOS| clear - SPH; lia| exact ST| exact MI|].
  cbv beta delta [mkR].
  zstep. zstep. zstep.
  unfold jn0_post, SITE_jn_new1, FZ_BIO_NEW, M_MEM, M_SECMEM, M_MEM_A, M_SECMEM_A, MEM_METHOD. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [left; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption| rewrite !firstn_firstn in FRE; exact FRE].
Qed.

(* [comment removed for export] *)
Lemma jn1_walk : forall sp1 gp t0 t1 t2 s0 hB a1 a2 a3 a4 a5 a6 a7 meth s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (wz SITE_jn_new2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz meth) a1 a2 a3 a4 a5 a6 a7 s2 (wz meth) s4 s5 s6 (wz hB) s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz FZ_BIO_NEW) fc None m (seg_rom asegs) /\ True)
    (MS (mkR (wz SITE_jn_new1) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz hB) a1 a2 a3 a4 a5 a6 a7 s2 (wz meth) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_jn_new1) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_jn_new1, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep.
  unfold SITE_jn_new2, FZ_BIO_NEW. apply evt_done. split; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
Definition jn2_post (sp1 : Z) (gp t0 t1 t2 s0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (dB : Z)
    (e64 : list byte) (c7 c8 c9 c10 c11 : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (wz SITE_jn_pmal) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz 256) s4 (wz 782) a3 a4 a5 a6 a7 s2 (wz dB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz FZ_PEM_MALLOC) fc None m' (seg_rom asegs)
    /\ munch [(sp1 + 112, sp1 + 216)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (sp1 + 112) [CB 16 (firstn 16 e64); C8 s5; CB 40 (skipn 24 e64); C8 c7; C8 c8; C8 c9; C8 c10; C8 c11].
Lemma jn2_walk : forall sp1 gp t0 t1 t2 s0 dB a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 hB s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (e64 : list byte) (c7 c8 c9 c10 c11 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < hB < 2 ^ 64 -> 0 < dB < 2 ^ 64 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [CB 64 e64; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11] ->
  evt asegs (jn2_post sp1 gp t0 t1 t2 s0 a3 a4 a5 a6 a7 s2 s4 s5 s6 (wz hB) s8 s9 s10 s11 t3 t4 t5 t6 F fc dB e64 c7 c8 c9 c10 c11 m)
    (MS (mkR (wz SITE_jn_new2) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz dB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz hB) s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_jn_new2) fc None m (seg_rom asegs)).
Proof.
  intros until c11. intros SP0 SPH HB DB MI FRE. unfold SITE_jn_new2, TP_A in *.
  pose proof (munch_refl [(sp1 + 112, sp1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 hB) = hB) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 dB) = dB) by (apply unsigned_lit; lia).
  zstep.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1 HB. lia. }
  zstep. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. clear - K2 DB. lia. }
  zstep; lfix. zstep. zstep. zstep. zstep.
  unfold jn2_post, SITE_jn_pmal, FZ_PEM_MALLOC. apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRE].
Qed.

(* [comment removed for export] *)
Definition jn3_post (sp1 : Z) (gp t0 t1 t2 s0 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (LB1 : Z)
    (cPN c7 c8 c9 c10 c11 cBI : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (wz SITE_jn_gets) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) cBI (wz LB1) (wz 255) a3 a4 a5 a6 a7 s2 s3 s4 (wz LB1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz FZ_BIO_GETS) fc None m' (seg_rom asegs)
    /\ munch [(sp1 + 112, sp1 + 216)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (sp1 + 112) [C8 s10; C8 s11; C8 cPN; C8 s2; C8 s7; C8 s3; C8 s6; C8 s4; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11].
Lemma jn3_walk : forall sp1 gp t0 t1 t2 s0 LB1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (e16 e40 : list byte) (cPN c7 c8 c9 c10 c11 cBI : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0 < LB1 < 2 ^ 64 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 112) [CB 16 e16; C8 cPN; CB 40 e40; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11] -> rw_cells asegs m (sp1 + 216) [C8 cBI] ->
  evt asegs (jn3_post sp1 gp t0 t1 t2 s0 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc LB1 cPN c7 c8 c9 c10 c11 cBI m)
    (MS (mkR (wz SITE_jn_pmal) (wz sp1) gp (wz TP_A) t0 t1 t2 s0 (wz sp1) (wz LB1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_jn_pmal) fc None m (seg_rom asegs)).
Proof.
  intros until cBI. intros SP0 SPH HL MI FRE FBI. unfold SITE_jn_pmal, TP_A in *.
  pose proof (munch_refl [(sp1 + 112, sp1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 LB1) = LB1) by (apply unsigned_lit; lia).
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1 HL. lia. }
  zstep. do 7 (zstep; lfix). zstep. zstep; lfix. zstep. zstep.
  unfold jn3_post, SITE_jn_gets, FZ_BIO_GETS. apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FRE].
Qed.

(* [comment removed for export] *)
Lemma jn4_walk_pos : forall ra sp1 gp t0 t1 t2 s0 s1 k a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  0 < k < 2 ^ 31 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_J0G) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz k) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_jn_gets) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HK MI. unfold SITE_jn_gets, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  assert (SK : bv_signed (Z_to_bv 64 k) = k) by (rewrite zb_signed, EK; destruct (Z.ltb_spec k (2 ^ 63)); lia).
  assert (S0 : bv_signed z64 = 0) by reflexivity.
  zstep. if_false.
  unfold J_J0G. apply evt_done. split; [reflexivity| exact I].
Qed.
(* [comment removed for export] *)
Lemma jn4_walk_zero : forall ra sp1 gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz J_RAISE1) fc None m (seg_rom asegs) /\ True)
    (MS (mkR ra (wz sp1) gp (wz TP_A) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz SITE_jn_gets) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold SITE_jn_gets, TP_A in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (S0 : bv_signed z64 = 0) by reflexivity.
  zstep. if_true.
  unfold J_RAISE1. apply evt_done. split; [reflexivity| exact I].
Qed.

Section CJ0n.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis C_BN : bio_new_mem_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_PM : pem_malloc_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_BG : bio_gets_stmt RT.
Hypothesis H_R1 : RAISE1_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis H_J0G : J0G_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_frame := (pem_frame RT).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma scratch_byte_facts : forall (en : pem_entry) Σ (m : mem) off crem lrem cur a,
  pem_com en Σ m off crem lrem cur -> e_lo RT en <= a < e_sp1 RT en ->
     aclient (rt_live RT Σ) (rt_frames RT Σ) (e_lo RT en) a
  /\ ~ aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a
  /\ ~ client_static a /\ ~ (0x7fff8000 <= a < 0x10007fff8000) /\ a < e_PL RT en - 104
  /\ (forall p n, In (p, n) (rt_live RT Σ) -> ~ (p <= a < p + n)).
Proof using AF AFP.
  intros en Σ m off crem lrem cur a COM Ha.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & REST).
  assert (ELV : incl_live (e_live RT en) (rt_live RT Σ)) by (intros e0 He0; apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; exact He0).
  unfold e_sp1 in *.
  split; [apply acl_stack; unfold USTACK_TOP, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *; lia|].
  split. { intros AC. destruct AC as [H|[H|[H|[H|H]]]].
    + lia.
    + pose proof (client_static_range a H). unfold SEGTOP_A, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
    + destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 (ELV _ Hin)) as (_ & X & _). unfold STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
    + destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
      pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (_ & X & _). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)). unfold fs_size, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
    + destruct H as (f & k & Hin & Hf). assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin).
      pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (X0 & X & _). pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)).
      unfold shad, SHB, fs_size, STACK_WIN, RT_STACK, PEM_CALLEE_STACK, USTACK_TOP in *. Z.div_mod_to_equations. lia. }
  split; [intros H; pose proof (client_static_range a H); unfold SEGTOP_A, STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *; lia|].
  split; [unfold STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *; lia|]. split; [lia|].
  intros p n Hin Hp. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & X & _). unfold STACK_WIN, RT_STACK, PEM_CALLEE_STACK in *. lia.
Qed.

(* [comment removed for export] *)
Lemma com_seg_sc : forall (en : pem_entry) Σ (m m' : mem) off crem lrem cur Wseg,
  pem_com en Σ m off crem lrem cur -> munch Wseg m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (e_lo RT en) (e_sp1 RT en) ->
  Forall (fun iv => seg_ok RT en cur iv \/ (e_lo RT en <= fst iv /\ snd iv <= e_sp1 RT en)) Wseg ->
  pem_com en Σ m' off crem lrem cur.
Proof using AF AFP libenv_agree libenv_fp_where.
  intros en Σ m m' off crem lrem cur Wseg COM MU WM MI' ST' HW.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (AGo : forall (P : Z -> Prop), (forall x iv, P x -> In iv Wseg -> ~ (fst iv <= x < snd iv)) -> agree_on P m m').
  { intros P HP a Ha. apply MU. apply outside_intro. intros iv Hiv. exact (HP _ _ Ha Hiv). }
  assert (HLO : e_lo RT en <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (BF : forall iv a, In iv Wseg -> fst iv <= a < snd iv ->
       aclient (rt_live RT Σ) (rt_frames RT Σ) (e_lo RT en) a /\ ~ aclient (e_live RT en) (e_frames RT en) (e_PL RT en) a
    /\ ~ client_static a /\ ~ (0x7fff8000 <= a < 0x10007fff8000) /\ a < e_PL RT en - 104 /\ (forall p n, In (p, n) (e_live RT en) -> ~ (p <= a < p + n))).
  { intros iv a Hiv Ha. destruct (proj1 (Forall_forall _ _) HW iv Hiv) as [OK|SC].
    - destruct (seg_byte_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m off crem lrem cur iv a COM OK Ha) as (A1 & A2 & A3 & A4 & A5 & A6).
      split; [| exact (conj A2 (conj A3 (conj A4 (conj A5 A6))))].
      destruct A1 as [H|H]; [apply acl_stack; lia| right; exact H].
    - destruct (scratch_byte_facts en Σ m off crem lrem cur a COM ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
      intros p n Hin. apply A6. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact Hin. }
  split. { apply (af_frame RT AF Σ m m' (e_lo RT en) ART0); [exact LOW| | exact WM].
           intros a NA. apply MU. apply outside_intro. intros iv Hiv R. exact (NA (proj1 (BF iv _ Hiv R))). }
  split; [exact MI'|]. split; [exact ST'|]. split; [exact PD|]. split; [exact PDM|]. split; [exact TOP|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact HLOS|].
  split. { eapply cl_env_seg; [exact CLE| exact MU|]. intros x Hx. apply outside_intro. intros iv Hiv R. exact (proj1 (proj2 (proj2 (BF iv x Hiv R))) (cl_cell_static _ Hx)). }
  split. { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply MU. apply outside_intro. intros iv Hiv R.
           apply (proj1 (proj2 (proj2 (BF iv _ Hiv R)))). apply client_static_intro. rewrite Ea. unfold SEC_INIT. lia. }
  split. { eapply libenv_agree; [exact LE|]. apply AGo. intros x iv Hx Hiv R. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p & n & Hin & Hp)].
           - exact (proj1 (proj2 (proj2 (BF iv x Hiv R))) CS).
           - exact (proj2 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) p n (INCL _ Hin) Hp). }
  split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|]. split; [exact NTL|].
  split. { eapply mbio_rep_agree; [exact MB|]. apply AGo. intros x iv (e & He & Hx) Hiv R. destruct e as [p n].
           exact (proj2 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) p n (KLV _ He) Hx). }
  split; [exact OFF|]. split; [exact BLT|]. split; [exact KLV|]. split; [exact PERM|]. split; [exact CFR|]. split; [exact ND|]. split; [exact LPOS|].
  split; [exact FRS|]. split; [exact FRN|]. split; [exact SP0|]. split; [exact CG|]. split; [exact LIV|]. split; [exact LR0|]. split; [exact CR|]. split; [exact CR0|]. split; [exact CRE|].
  split; [exact CGH|]. split; [exact CGS|]. split; [exact CTX|].
  split. { eapply uw_chain_agree; [exact UWC|]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx.
           pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (BF iv _ Hiv R)))))). unfold e_PL in *. lia. }
  split; [exact F0|]. split; [exact F64|]. split; [exact FTOP|]. split; [exact FSEG|]. split; [exact FSH|].
  split. { eapply rw_cells_agree; [exact FFS| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx.
           pose proof (proj1 (proj2 (proj2 (proj2 (BF iv x Hiv R))))) as NS. apply NS. unfold ff_shadow in Hx. cbn [cells_size csize Nat.add] in Hx.
           pose proof (af_sp0_range RT AF Σ m ART0). pose proof (af_sp0_win RT AF Σ m ART0). unfold shad, SHB, USTACK_TOP, STACK_WIN in *.
           clear - Hx F0 FTOP. Z.div_mod_to_equations. lia. }
  split. { eapply rw_cells_agree; [exact SAVED| | exact WM]. apply AGo. intros x iv Hx Hiv R. cbv beta in Hx. unfold pem_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
           pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (BF iv x Hiv R)))))). lia. }
  split. { eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply MU. apply outside_intro. intros iv Hiv R. exact (proj1 (proj2 (BF iv _ Hiv R)) Ha). }
  split; [exact FLR|]. split; [exact NDO|]. split; [exact OUTS|]. split; [exact FDO| exact MST].
Qed.

(* [comment removed for export] *)
Lemma lo_win_facts : forall (en : pem_entry) Σ (m : mem) off crem lrem cur (W : list (Z * Z)),
  pem_com en Σ m off crem lrem cur -> (forall x, (x < e_lo RT en \/ e_PL RT en - 104 <= x) -> outside W x) ->
     (forall p n x, In (p, n) (rt_live RT Σ) -> p <= x < p + n -> outside W x)
  /\ (forall x, e_f RT en <= x < e_f RT en + 128 -> outside W x)
  /\ (forall P x, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> P <= x < P + 8 -> outside W x).
Proof using AF AFP.
  intros en Σ m off crem lrem cur W COM HW.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  split. { intros p n x Hin Hx. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & R & _). apply HW. left. clear - R Hx LOW. unfold STACK_WIN in *. lia. }
  split. { intros x Hx. pose proof (af_frames_range RT AF Σ m _ _ ART0 INF) as (_ & R & _). change (fs_size 1) with 128 in R. apply HW. left.
           clear - R Hx LOW. unfold STACK_WIN in *. lia. }
  intros P x HP Hx. assert (HL : pp_loc (e_frames RT en) (e_m RT en) USTACK_TOP P) by exact (proj2 (proj1 (Forall_forall _ _) OUTS P HP)).
  destruct HL as [[H1 H2]|(f & k & Hin & H1 & H2 & _)].
  - exfalso. clear - H1 H2. lia.
  - assert (Hin' : In (f, k) (rt_frames RT Σ)) by (rewrite FRS; right; exact Hin). pose proof (af_frames_range RT AF Σ m f k ART0 Hin') as (_ & R & _).
    apply HW. left. clear - R H1 H2 Hx LOW. unfold STACK_WIN in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem J0N_proof : J0N_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros en Σ m crem lrem j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F fc xra t0 t1 t2 a0 a1 a6 a7 s7 t3 t4 t5 t6 lE.
  intros COM ER0 CRM LRM FR0 FRH SZH FRF SZF FR104 FRE SZE FBI FR224 FRG FFC ON. unfold pem_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & NTL & MB & OFF & BLT & KLV & PERM & CFR & ND & LPOS
     & FRS & FRN & SP0 & CG & LIV & LR0 & CR & CR0 & CRE & CGH & CGS & CTX & UWC & F0 & F64 & FTOP & FSEG & FSH & FFS & SAVED & PRES & FLR & NDO & OUTS & FDO & MST).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m (e_boff RT en) crem lrem _ COM) as [ELV CLV].
  assert (HLO : e_lo RT en + 16 <= e_sp1 RT en) by (clear - LOR; unfold RT_STACK, PEM_CALLEE_STACK in *; lia).
  assert (INF : In (e_f RT en, 1%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (SP0' : 0 <= e_sp1 RT en) by (clear - HLO HLOS; lia). assert (SPH : e_sp1 RT en + 368 <= 2 ^ 47) by (clear - TOP PD; unfold e_sp1, USTACK_TOP in *; lia).
  assert (FH : e_f RT en + 128 < 2 ^ 47) by (clear - FTOP; unfold USTACK_TOP in FTOP; lia).
  assert (G255 : 255 < gr_n (0 + 255)) by (apply gr_n_gt; clear; lia).
  assert (GP0 : 0 <= grow_pot RT en 0 0) by (apply (grow_pot_nonneg RT en 0 0 0 0 (e_boff RT en) ltac:(clear - OFF; lia)); clear - G255 OFF; lia).
  assert (CR3 : 3 <= crem) by (clear - CRM GP0 OFF BLT; unfold gn_need, C_END in CRM; lia).
  (* [comment removed for export] *)
  pose proof (rw_cells_blur m (e_sp1 RT en + 112) lE [] ltac:(rewrite app_nil_r; exact FRE)) as FREB.
  replace (cells_size lE) with 104%nat in FREB by (clear - SZE; lia).
  (* [comment removed for export] *)
  pose proof (jn0_walk xra (e_sp1 RT en) (e_gp RT en) t0 t1 t2 (e_sp RT en) a0 a1 a6 a7 (wz (e_f RT en)) (wz (e_PN RT en)) (wz (e_f RT en)) s7
                (wz (shad (e_f RT en))) (wz SHB) (wz (e_PD RT en)) (wz (e_PH RT en)) t3 t4 t5 t6 F fc m (e_flags RT en) (e_lo RT en) (cells_bytes lE)
                (wz (shad (e_PN RT en))) (wz (shad (e_PLN RT en))) (wz (e_PLN RT en)) (wz (shad (e_PD RT en))) (wz (shad (e_PH RT en)))
                HLOS HLO SPH FLR MI ST FREB) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & meth & m1 & -> & HM & MU1 & WM1 & MI1 & ST1 & FRE1) & Hc1'). clear Hc1. try clear HA.
  set (W1 := [(e_sp1 RT en - 16, e_sp1 RT en); (e_sp1 RT en + 112, e_sp1 RT en + 216)]) in *.
  assert (HW1 : forall x, (x < e_lo RT en \/ e_PL RT en - 104 <= x) -> outside W1 x) by (intros x Hx; subst W1; cbn; unfold e_sp1 in *; clear - Hx PD HLO; lia).
  destruct (lo_win_facts en Σ m (e_boff RT en) crem lrem _ W1 COM HW1) as (W1L & W1F & W1O).
  assert (KP1 : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W1 x) -> rw_cells asegs m1 A cs).
  { intros A cs C HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU1. exact (HO _ Ha). }
  assert (PR1 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (e_sp1 RT en) W1 m m1) by (intros a _ Ho; exact (MU1 a Ho)).
  assert (COM1 : pem_com en Σ m1 (e_boff RT en) crem lrem []).
  { eapply (com_seg_sc en Σ m m1); [exact COM| exact MU1| exact WM1| exact MI1| exact ST1|].
    subst W1. apply Forall_cons; [right; cbn [fst snd]; clear - HLO; lia|]. apply Forall_cons; [| apply Forall_nil]. left; left; cbn [fst snd]; unfold e_sp1 in *; clear - PD; lia. }
  assert (ER1 : errst_at_rest (e_E RT en) [] m1).
  { eapply (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS en Σ m m1); [exact COM| exact ER0| exact PR1| exact (ELV _ INE)| intros x Hx; exact (W1L _ _ x (ELV _ INE) Hx)]. }
  assert (FFC1 : rw_cells asegs m1 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
  { apply (KP1 _ _ FFC). unfold ff_cells. cbn [cells_size csize Nat.add]. intros x Hx. apply W1F. clear - Hx. lia. }
  assert (G8_1 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m P [C8 vv] -> rw_cells asegs m1 P [C8 vv]).
  { intros P vv HPP C. apply (KP1 _ _ C). cbn [cells_size csize Nat.add]. intros x Hx. apply (W1O P x HPP). clear - Hx. lia. }
  assert (ON1 : out_null RT en m1).
  { destruct ON as (O1 & O2 & O3 & O4). split; [apply G8_1; [cbn; tauto| exact O1]|]. split; [apply G8_1; [cbn; tauto| exact O2]|]. split; [apply G8_1; [cbn; tauto| exact O3]|]. apply G8_1; [cbn; tauto| exact O4]. }
  assert (OWN1 : forall A cs, rw_cells asegs m A cs -> e_sp1 RT en <= A -> A + Z.of_nat (cells_size cs) <= e_sp1 RT en + 112 \/ (e_sp1 RT en + 216 <= A /\ A + Z.of_nat (cells_size cs) <= e_PL RT en) -> rw_cells asegs m1 A cs).
  { intros A cs C H1 H2. apply (KP1 _ _ C). intros x Hx. subst W1. cbn. clear - Hx H1 H2. lia. }
  pose proof (OWN1 _ _ FR0 ltac:(clear; lia) ltac:(left; cbn [cells_size csize Nat.add]; clear; lia)) as FR0_1.
  pose proof (OWN1 _ _ FRH ltac:(clear; lia) ltac:(left; rewrite SZH; clear; lia)) as FRH_1.
  pose proof (OWN1 _ _ FRF ltac:(clear; lia) ltac:(left; rewrite SZF; clear; lia)) as FRF_1.
  pose proof (OWN1 _ _ FR104 ltac:(clear; lia) ltac:(left; cbn [cells_size csize Nat.add]; clear; lia)) as FR104_1.
  pose proof (OWN1 _ _ FBI ltac:(clear; lia) ltac:(right; cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FBI_1.
  pose proof (OWN1 _ _ FR224 ltac:(clear; lia) ltac:(right; cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR224_1.
  pose proof (OWN1 _ _ FRG ltac:(clear; lia) ltac:(right; cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FRG_1.
  clear COM ER0 FFC ON FR0 FRH FRF FR104 FBI FR224 FRG FRE FREB KP1 OWN1 G8_1 W1L W1F W1O HW1 PR1 MU1 WM1 ST1 MI ST.
  (* [comment removed for export] *)
  eapply (pem_call_bnew RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BN T en Σ m1 (e_boff RT en) crem lrem [] meth SITE_jn_new1
            F fc u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 (wz (e_f RT en)) (wz meth) (wz (e_flags RT en)) (wz (e_PN RT en)) (wz (e_f RT en)) s7 (wz (e_PD RT en)) (wz (e_PH RT en)) u3 u4 u5 u6 c1
            COM1 HM ltac:(clear - CR3; lia) ltac:(clear - LRM; lia) ltac:(unfold PEM_RAS_new, SITE_jn_new1; left; reflexivity) Hc1').
  clear Hc1' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6.
  intros Σ2 m2 F2 fc2 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c2 KX BIx BBx BMx RPx COM2 HKX LV2 FRS2 PR2 MBX Hc2.
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 (e_boff RT en) crem lrem _ COM1) as (HWS1 & HWFR1 & HWFF1 & HWF1 & HWL1 & HWP1).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ m1 (e_boff RT en) crem lrem _ COM1) as [ELV1 CLV1].
  assert (SK2 : forall A cs, rw_cells asegs m1 A cs -> e_sp1 RT en <= A -> A + Z.of_nat (cells_size cs) <= e_PL RT en -> rw_cells asegs m2 A cs).
  { intros A cs C H1 H2. eapply stack_keep; [exact C| exact PR2| exact H1| clear - H2 TOP; lia|]. intros x Hx. apply HWS1. clear - Hx H1 H2 TOP. lia. }
  assert (ER2 : errst_at_rest (e_E RT en) [] m2).
  { eapply (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS en Σ m1 m2); [exact COM1| exact ER1| exact PR2| exact (ELV1 _ INE)| exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 (e_boff RT en) crem lrem _ COM1)]. }
  assert (FFC2 : rw_cells asegs m2 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m1 m2 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC1 PR2 INF HWFF1).
  assert (ON2 : out_null RT en m2).
  { destruct ON1 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ m1 m2 (e_boff RT en) crem lrem _ _ _ COM1 HWS1 HWFR1 PR2) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m1 P [C8 vv] -> rw_cells asegs m2 P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  pose proof (SK2 _ _ FR0_1 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR0_2.
  pose proof (SK2 _ _ FRH_1 ltac:(clear; lia) ltac:(rewrite SZH; unfold e_sp1; clear - PD; lia)) as FRH_2.
  pose proof (SK2 _ _ FRF_1 ltac:(clear; lia) ltac:(rewrite SZF; unfold e_sp1; clear - PD; lia)) as FRF_2.
  pose proof (SK2 _ _ FR104_1 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR104_2.
  pose proof (SK2 _ _ FRE1 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FRE2.
  pose proof (SK2 _ _ FBI_1 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FBI_2.
  pose proof (SK2 _ _ FR224_1 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR224_2.
  pose proof (SK2 _ _ FRG_1 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FRG_2.
  clear COM1 ER1 FFC1 ON1 FR0_1 FRH_1 FRF_1 FR104_1 FRE1 FBI_1 FR224_1 FRG_1 SK2 HWS1 HWFR1 HWFF1 HWF1 HWL1 HWP1 ELV1 CLV1 MI1.
  pose proof COM2 as (ART2 & MI2 & _).
  (* [comment removed for export] *)
  pose proof (jn1_walk (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) BIx d1 d2 d3 d4 d5 d6 d7 meth (wz (e_f RT en)) (wz (e_flags RT en)) (wz (e_PN RT en))
                (wz (e_f RT en)) s7 (wz (shad (e_f RT en))) (wz SHB) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 F2 fc2 m2 MI2) as W1w.
  cl_lift W1w Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & (-> & _) & Hc3'). clear Hc3 Hc2.
  (* [comment removed for export] *)
  eapply (pem_call_bnew RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BN T en Σ2 m2 (e_boff RT en) (crem - 1) (lrem - 4) _ meth SITE_jn_new2
            F2 fc2 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 (wz (e_f RT en)) (wz meth) (wz (e_flags RT en)) (wz (e_PN RT en)) (wz (e_f RT en)) (wz BIx) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 c3
            COM2 HM ltac:(clear - CR3; lia) ltac:(clear - LRM; lia) ltac:(unfold PEM_RAS_new, SITE_jn_new2; right; left; reflexivity) Hc3').
  clear Hc3' y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6.
  intros Σ3 m3 F3 fc3 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c4 KY BIy BBy BMy RPy COM3 HKY LV3 FRS3 PR3 MBY Hc4.
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m2 (e_boff RT en) (crem - 1) (lrem - 4) _ COM2) as (HWS2 & HWFR2 & HWFF2 & HWF2 & HWL2 & HWP2).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ2 m2 (e_boff RT en) (crem - 1) (lrem - 4) _ COM2) as [ELV2 CLV2].
  assert (INF2 : In (e_f RT en, 1%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  assert (SK3 : forall A cs, rw_cells asegs m2 A cs -> e_sp1 RT en <= A -> A + Z.of_nat (cells_size cs) <= e_PL RT en -> rw_cells asegs m3 A cs).
  { intros A cs C H1 H2. eapply stack_keep; [exact C| exact PR3| exact H1| clear - H2 TOP; lia|]. intros x Hx. apply HWS2. clear - Hx H1 H2 TOP. lia. }
  assert (ER3 : errst_at_rest (e_E RT en) [] m3).
  { eapply (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS en Σ2 m2 m3); [exact COM2| exact ER2| exact PR3| exact (ELV2 _ INE)| exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m2 (e_boff RT en) (crem - 1) (lrem - 4) _ COM2)]. }
  assert (FFC3 : rw_cells asegs m3 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m2 m3 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC2 PR3 INF2 HWFF2).
  assert (ON3 : out_null RT en m3).
  { destruct ON2 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m2 m3 (e_boff RT en) (crem - 1) (lrem - 4) _ _ _ COM2 HWS2 HWFR2 PR3) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m2 P [C8 vv] -> rw_cells asegs m3 P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  assert (MBX3 : mbio_rep (rt_live RT Σ3) m3 KX BIx meth 0 0 0).
  { eapply (mbio_rep_keep (rt_live RT Σ2)); [exact MBX| exact PR3| intros e He; rewrite LV3; split; [| do 4 right]; apply CLV2; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ2 m2 (e_boff RT en) (crem - 1) (lrem - 4) _ _ _ COM2 HWL2 (fun e0 H0 => or_intror H0) e x ltac:(apply in_or_app; left; exact He) Hx). }
  pose proof (SK3 _ _ FR0_2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR0_3.
  pose proof (SK3 _ _ FRH_2 ltac:(clear; lia) ltac:(rewrite SZH; unfold e_sp1; clear - PD; lia)) as FRH_3.
  pose proof (SK3 _ _ FRF_2 ltac:(clear; lia) ltac:(rewrite SZF; unfold e_sp1; clear - PD; lia)) as FRF_3.
  pose proof (SK3 _ _ FR104_2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR104_3.
  pose proof (SK3 _ _ FRE2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FRE3.
  pose proof (SK3 _ _ FBI_2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FBI_3.
  pose proof (SK3 _ _ FR224_2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR224_3.
  pose proof (SK3 _ _ FRG_2 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FRG_3.
  clear COM2 ER2 FFC2 ON2 MBX FR0_2 FRH_2 FRF_2 FR104_2 FRE2 FBI_2 FR224_2 FRG_2 SK3 HWS2 HWFR2 HWFF2 HWF2 HWL2 HWP2 ELV2 CLV2 MI2 ART2 PR2 PR3.
  pose proof COM3 as (ART3 & MI3 & ST3 & _).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ3 m3 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ COM3) as [ELV3 CLV3].
  (* [comment removed for export] *)
  assert (HBX : In (BIx, 128) (mbio_ent KY 0 ++ mbio_ent KX 0 ++ [])) by (apply in_or_app; right; apply in_or_app; left; subst KX; cbn; left; reflexivity).
  assert (HBY : In (BIy, 128) (mbio_ent KY 0 ++ mbio_ent KX 0 ++ [])) by (apply in_or_app; left; subst KY; cbn; left; reflexivity).
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ3 m3 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ (BIx, 128) COM3 HBX ltac:(cbn; lia)) as (_ & X0 & XLO & _ & _). cbn [fst snd] in X0, XLO.
  pose proof (cur_live_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ3 m3 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ (BIy, 128) COM3 HBY ltac:(cbn; lia)) as (_ & Y0 & YLO & _ & _). cbn [fst snd] in Y0, YLO.
  (* [comment removed for export] *)
  pose proof (jn2_walk (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) BIy d1 d2 d3 d4 d5 d6 d7 (wz (e_f RT en)) (wz meth) (wz (e_flags RT en)) (wz (e_PN RT en))
                (wz (e_f RT en)) BIx (wz (shad (e_f RT en))) (wz SHB) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 F3 fc3 m3 (firstn 64 (cells_bytes lE)) _ _ _ _ _
                SP0' SPH ltac:(clear - X0 XLO HLO SPH; lia) ltac:(clear - Y0 YLO HLO SPH; lia) MI3 FRE3) as W2w.
  cl_lift W2w Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ3 _ _ c5 Hc5) as (ms5 & (m4 & -> & MU4 & WM4 & MI4 & FRE4) & Hc5'). clear Hc5 Hc4.
  set (W4 := [(e_sp1 RT en + 112, e_sp1 RT en + 216)]) in *.
  assert (HW4 : forall x, (x < e_sp1 RT en \/ e_PL RT en - 104 <= x) -> outside W4 x) by (intros x Hx; subst W4; cbn; unfold e_sp1 in *; clear - Hx PD; lia).
  destruct (stk_win_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ3 m3 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ W4 COM3 HW4) as (W4L & W4F & W4O).
  assert (KP4 : forall A cs, rw_cells asegs m3 A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W4 x) -> rw_cells asegs m4 A cs).
  { intros A cs C HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU4. exact (HO _ Ha). }
  assert (PR4 : rt_pres_fp (rt_live RT Σ3) (rt_frames RT Σ3) (e_sp1 RT en) W4 m3 m4) by (intros a _ Ho; exact (MU4 a Ho)).
  assert (ST4 : stk asegs m4 (e_lo RT en) (e_sp1 RT en)).
  { eapply stk_munch; [exact ST3| exact MU4| exact WM4|]. intros x Hx. apply HW4. left. clear - Hx. lia. }
  assert (COM4 : pem_com en Σ3 m4 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) (mbio_ent KY 0 ++ mbio_ent KX 0 ++ [])).
  { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ3 m3 m4); [exact COM3| exact MU4| exact WM4| exact MI4| exact ST4|].
    subst W4. apply Forall_cons; [| apply Forall_nil]. left; cbn [fst snd]; unfold e_sp1 in *; clear - PD; lia. }
  assert (ER4 : errst_at_rest (e_E RT en) [] m4).
  { eapply (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS en Σ3 m3 m4); [exact COM3| exact ER3| exact PR4| exact (ELV3 _ INE)| intros x Hx; exact (W4L _ _ x (ELV3 _ INE) Hx)]. }
  assert (FFC4 : rw_cells asegs m4 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
  { apply (KP4 _ _ FFC3). unfold ff_cells. cbn [cells_size csize Nat.add]. intros x Hx. apply W4F. clear - Hx. lia. }
  assert (ON4 : out_null RT en m4).
  { destruct ON3 as (O1 & O2 & O3 & O4).
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m3 P [C8 vv] -> rw_cells asegs m4 P [C8 vv]).
    { intros P vv HPP C. apply (KP4 _ _ C). cbn [cells_size csize Nat.add]. intros x Hx. apply (W4O P x HPP). clear - Hx. lia. }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  assert (MBX4 : mbio_rep (rt_live RT Σ3) m4 KX BIx meth 0 0 0).
  { eapply (mbio_rep_keep (rt_live RT Σ3)); [exact MBX3| exact PR4| intros e He; split; apply CLV3; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros [p n] x He Hx. exact (W4L p n x (CLV3 _ ltac:(apply in_or_app; right; apply in_or_app; left; exact He)) Hx). }
  assert (MBY4 : mbio_rep (rt_live RT Σ3) m4 KY BIy meth 0 0 0).
  { eapply (mbio_rep_keep (rt_live RT Σ3)); [exact MBY| exact PR4| intros e He; split; apply CLV3; apply in_or_app; left; exact He|].
    intros [p n] x He Hx. exact (W4L p n x (CLV3 _ ltac:(apply in_or_app; left; exact He)) Hx). }
  assert (OWN4 : forall A cs, rw_cells asegs m3 A cs -> A + Z.of_nat (cells_size cs) <= e_sp1 RT en + 112 \/ e_sp1 RT en + 216 <= A -> rw_cells asegs m4 A cs).
  { intros A cs C H2. apply (KP4 _ _ C). intros x Hx. subst W4. cbn. clear - Hx H2. lia. }
  pose proof (OWN4 _ _ FR0_3 ltac:(left; cbn [cells_size csize Nat.add]; clear; lia)) as FR0_4.
  pose proof (OWN4 _ _ FRH_3 ltac:(left; rewrite SZH; clear; lia)) as FRH_4.
  pose proof (OWN4 _ _ FRF_3 ltac:(left; rewrite SZF; clear; lia)) as FRF_4.
  pose proof (OWN4 _ _ FR104_3 ltac:(left; cbn [cells_size csize Nat.add]; clear; lia)) as FR104_4.
  pose proof (OWN4 _ _ FBI_3 ltac:(right; clear; lia)) as FBI_4.
  pose proof (OWN4 _ _ FR224_3 ltac:(right; clear; lia)) as FR224_4.
  pose proof (OWN4 _ _ FRG_3 ltac:(right; clear; lia)) as FRG_4.
  clear COM3 ER3 FFC3 ON3 MBX3 MBY FR0_3 FRH_3 FRF_3 FR104_3 FRE3 FBI_3 FR224_3 FRG_3 KP4 OWN4 W4L W4F W4O HW4 PR4 MU4 WM4 ST3 ST4 MI3 ART3 ELV3 CLV3.
  (* [comment removed for export] *)
  assert (MC0 : mcost 256 = 0) by reflexivity.
  eapply (pem_call_pmal RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_PM T en Σ3 m4 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ 256 SITE_jn_pmal F3 fc3
            y0 y1 y2 (wz 782) d3 d4 d5 d6 d7 (wz (e_f RT en)) (wz BIy) (wz (e_flags RT en)) (wz (e_PN RT en)) (wz (e_f RT en)) (wz BIx) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 c5 COM4
            ltac:(clear; lia) ltac:(rewrite MC0; clear - CR3; lia) ltac:(clear - LRM; lia) ltac:(unfold PEM_RAS_pmal, SITE_jn_pmal; left; reflexivity) Hc5').
  clear Hc5' y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6.
  intros Σ5 m5 F5 fc5 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c6 LB1 junk COM5 LV5 FRS5 PR5 LNJ LBC5 L0 AL16 LTOP Hc6. rewrite MC0, Z.sub_0_r in COM5.
  pose proof (com_W_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ3 m4 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ COM4) as (HWS4 & HWFR4 & HWFF4 & HWF4 & HWL4 & HWP4).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ3 m4 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ COM4) as [ELV4 CLV4].
  assert (INF3 : In (e_f RT en, 1%nat) (rt_frames RT Σ3)) by (rewrite FRS3, FRS2; exact INF).
  assert (SK5 : forall A cs, rw_cells asegs m4 A cs -> e_sp1 RT en <= A -> A + Z.of_nat (cells_size cs) <= e_PL RT en -> rw_cells asegs m5 A cs).
  { intros A cs C H1 H2. eapply stack_keep; [exact C| exact PR5| exact H1| clear - H2 TOP; lia|]. intros x Hx. apply HWS4. clear - Hx H1 H2 TOP. lia. }
  assert (ER5 : errst_at_rest (e_E RT en) [] m5).
  { eapply (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS en Σ3 m4 m5); [exact COM4| exact ER4| exact PR5| exact (ELV4 _ INE)| exact (com_E_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ3 m4 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ COM4)]. }
  assert (FFC5 : rw_cells asegs m5 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m4 m5 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC4 PR5 INF3 HWFF4).
  assert (ON5 : out_null RT en m5).
  { destruct ON4 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ3 m4 m5 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ _ _ COM4 HWS4 HWFR4 PR5) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m4 P [C8 vv] -> rw_cells asegs m5 P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  assert (MBX5 : mbio_rep (rt_live RT Σ5) m5 KX BIx meth 0 0 0).
  { eapply (mbio_rep_keep (rt_live RT Σ3)); [exact MBX4| exact PR5| intros e He; rewrite LV5; split; [| right]; apply CLV4; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ3 m4 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ _ _ COM4 HWL4 (fun e0 H0 => or_intror H0) e x ltac:(apply in_or_app; right; apply in_or_app; left; exact He) Hx). }
  assert (MBY5 : mbio_rep (rt_live RT Σ5) m5 KY BIy meth 0 0 0).
  { eapply (mbio_rep_keep (rt_live RT Σ3)); [exact MBY4| exact PR5| intros e He; rewrite LV5; split; [| right]; apply CLV4; apply in_or_app; left; exact He|].
    intros e x He Hx. exact (com_cur_out RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ3 m4 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4) _ _ _ COM4 HWL4 (fun e0 H0 => or_intror H0) e x ltac:(apply in_or_app; left; exact He) Hx). }
  pose proof (SK5 _ _ FR0_4 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR0_5.
  pose proof (SK5 _ _ FRH_4 ltac:(clear; lia) ltac:(rewrite SZH; unfold e_sp1; clear - PD; lia)) as FRH_5.
  pose proof (SK5 _ _ FRF_4 ltac:(clear; lia) ltac:(rewrite SZF; unfold e_sp1; clear - PD; lia)) as FRF_5.
  pose proof (SK5 _ _ FR104_4 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR104_5.
  pose proof (SK5 _ _ FRE4 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FRE5.
  pose proof (SK5 _ _ FBI_4 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FBI_5.
  pose proof (SK5 _ _ FR224_4 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FR224_5.
  pose proof (SK5 _ _ FRG_4 ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; unfold e_sp1; clear - PD; lia)) as FRG_5.
  clear COM4 ER4 FFC4 ON4 MBX4 MBY4 FR0_4 FRH_4 FRF_4 FR104_4 FRE4 FBI_4 FR224_4 FRG_4 SK5 HWS4 HWFR4 HWFF4 HWF4 HWL4 HWP4 ELV4 CLV4 MI4 PR5.
  pose proof COM5 as (ART5 & MI5 & ST5 & _).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ5 m5 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4 - 1) _ COM5) as [ELV5 CLV5].
  (* [comment removed for export] *)
  assert (HLB : In (LB1, 256) ((LB1, 256) :: mbio_ent KY 0 ++ mbio_ent KX 0 ++ [])) by (left; reflexivity).
  pose proof (jn3_walk (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) LB1 d1 d2 d3 d4 d5 d6 d7 (wz (e_f RT en)) (wz BIy) (wz (e_flags RT en)) (wz (e_PN RT en))
                (wz (e_f RT en)) (wz BIx) (wz (shad (e_f RT en))) (wz SHB) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 F5 fc5 m5 _ _ _ _ _ _ _ _ _
                SP0' SPH ltac:(clear - L0 LTOP; unfold USTACK_TOP in LTOP; lia) MI5 FRE5 FBI_5) as W3w.
  cl_lift W3w Hc6 c7 Hc7. destruct (ASTA_unpack RT Σ5 _ _ c7 Hc7) as (ms7 & (m6 & -> & MU6 & WM6 & MI6 & FRE6) & Hc7'). clear Hc7 Hc6.
  set (W6 := [(e_sp1 RT en + 112, e_sp1 RT en + 216)]) in *.
  assert (HW6 : forall x, (x < e_sp1 RT en \/ e_PL RT en - 104 <= x) -> outside W6 x) by (intros x Hx; subst W6; cbn; unfold e_sp1 in *; clear - Hx PD; lia).
  destruct (stk_win_facts RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ5 m5 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4 - 1) _ W6 COM5 HW6) as (W6L & W6F & W6O).
  assert (KP6 : forall A cs, rw_cells asegs m5 A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W6 x) -> rw_cells asegs m6 A cs).
  { intros A cs C HO. eapply rw_cells_agree_nw; [exact C|]. intros a Ha. apply MU6. exact (HO _ Ha). }
  assert (PR6 : rt_pres_fp (rt_live RT Σ5) (rt_frames RT Σ5) (e_sp1 RT en) W6 m5 m6) by (intros a _ Ho; exact (MU6 a Ho)).
  assert (ST6 : stk asegs m6 (e_lo RT en) (e_sp1 RT en)).
  { eapply stk_munch; [exact ST5| exact MU6| exact WM6|]. intros x Hx. apply HW6. left. clear - Hx. lia. }
  assert (COM6 : pem_com en Σ5 m6 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4 - 1) ((LB1, 256) :: mbio_ent KY 0 ++ mbio_ent KX 0 ++ [])).
  { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ5 m5 m6); [exact COM5| exact MU6| exact WM6| exact MI6| exact ST6|].
    subst W6. apply Forall_cons; [| apply Forall_nil]. left; cbn [fst snd]; unfold e_sp1 in *; clear - PD; lia. }
  assert (ER6 : errst_at_rest (e_E RT en) [] m6).
  { eapply (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS en Σ5 m5 m6); [exact COM5| exact ER5| exact PR6| exact (ELV5 _ INE)| intros x Hx; exact (W6L _ _ x (ELV5 _ INE) Hx)]. }
  assert (FFC6 : rw_cells asegs m6 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)).
  { apply (KP6 _ _ FFC5). unfold ff_cells. cbn [cells_size csize Nat.add]. intros x Hx. apply W6F. clear - Hx. lia. }
  assert (ON6 : out_null RT en m6).
  { destruct ON5 as (O1 & O2 & O3 & O4).
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m5 P [C8 vv] -> rw_cells asegs m6 P [C8 vv]).
    { intros P vv HPP C. apply (KP6 _ _ C). cbn [cells_size csize Nat.add]. intros x Hx. apply (W6O P x HPP). clear - Hx. lia. }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  assert (MBX6 : mbio_rep (rt_live RT Σ5) m6 KX BIx meth 0 0 0).
  { eapply (mbio_rep_keep (rt_live RT Σ5)); [exact MBX5| exact PR6| intros e He; split; apply CLV5; right; apply in_or_app; right; apply in_or_app; left; exact He|].
    intros [p n] x He Hx. exact (W6L p n x (CLV5 _ ltac:(right; apply in_or_app; right; apply in_or_app; left; exact He)) Hx). }
  assert (MBY6 : mbio_rep (rt_live RT Σ5) m6 KY BIy meth 0 0 0).
  { eapply (mbio_rep_keep (rt_live RT Σ5)); [exact MBY5| exact PR6| intros e He; split; apply CLV5; right; apply in_or_app; left; exact He|].
    intros [p n] x He Hx. exact (W6L p n x (CLV5 _ ltac:(right; apply in_or_app; left; exact He)) Hx). }
  assert (LBC6 : rw_cells asegs m6 LB1 [CB 256 junk]).
  { apply (KP6 _ _ LBC5). cbn [cells_size csize]. intros x Hx. apply (W6L LB1 256 x (CLV5 _ HLB)). clear - Hx. lia. }
  (* [comment removed for export] *)
  assert (PFR6 : pem_frame en m6 j0 lH lF endv BIx BIy x1 x2 gap).
  { split; [apply (KP6 _ _ FR0_5); cbn [cells_size csize Nat.add]; intros x Hx; subst W6; cbn; clear - Hx; lia|].
    split; [apply (KP6 _ _ FRH_5); rewrite SZH; intros x Hx; subst W6; cbn; clear - Hx; lia|]. split; [exact SZH|].
    split; [apply (KP6 _ _ FRF_5); rewrite SZF; intros x Hx; subst W6; cbn; clear - Hx; lia|]. split; [exact SZF|].
    split; [apply (KP6 _ _ FR104_5); cbn [cells_size csize Nat.add]; intros x Hx; subst W6; cbn; clear - Hx; lia|].
    split. { unfold loc_E. apply (proj2 (rw_cells_app m6 (e_sp1 RT en + 112)
                 [C8 (wz (e_PD RT en)); C8 (wz (e_PH RT en)); C8 (wz (e_PN RT en)); C8 (wz (e_f RT en)); C8 (wz BIx); C8 (wz BIy); C8 (wz (e_f RT en)); C8 (wz (e_flags RT en));
                  C8 (wz (shad (e_PN RT en))); C8 (wz (shad (e_PLN RT en))); C8 (wz (e_PLN RT en)); C8 (wz (shad (e_PD RT en))); C8 (wz (shad (e_PH RT en)))] [C8 (wz (e_BI RT en))])).
             split; [exact FRE6|]. cbn [cells_size csize Nat.add]. replace (e_sp1 RT en + 112 + Z.of_nat 104) with (e_sp1 RT en + 216) by (clear; lia).
             apply (KP6 _ _ FBI_5). cbn [cells_size csize Nat.add]. intros x Hx. subst W6. cbn. clear - Hx. lia. }
    split; [apply (KP6 _ _ FR224_5); cbn [cells_size csize Nat.add]; intros x Hx; subst W6; cbn; clear - Hx; lia|].
    apply (KP6 _ _ FRG_5). cbn [cells_size csize]. intros x Hx. subst W6. cbn. clear - Hx PD. lia. }
  clear COM5 ER5 FFC5 ON5 MBX5 MBY5 LBC5 FR0_5 FRH_5 FRF_5 FR104_5 FRE5 FRE6 FBI_5 FR224_5 FRG_5 KP6 W6L W6F W6O HW6 PR6 MU6 WM6 ST5 ST6 MI5 ART5.
  pose proof COM6 as (ART6 & MI6' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PERM6 & CFR6 & ND6 & _).
  destruct (com_lists RT libenv FZ_SITES FZ_CALLS en Σ5 m6 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4 - 1) _ COM6) as [ELV6 CLV6].
  (* [comment removed for export] *)
  pose proof ND6 as ND'. cbn [map fst app] in ND'. rewrite !map_app, !mbio_ent_fst in ND'. rewrite ?app_nil_r in ND'.
  apply List.NoDup_cons_iff in ND'. destruct ND' as [NQL ND2]. rewrite <- !app_assoc in ND2. cbn [app] in ND2.
  pose proof (nd_split _ _ ND2) as (NDY & ND3 & DJY). pose proof (nd_split _ _ ND3) as (NDX & ND4 & DJX). apply List.NoDup_cons_iff in ND4. destruct ND4 as [NQE _].
  assert (NXL : forall e, In e (mbio_ent KX 0) -> ~ In e ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros e He [<-|X]; pose proof (in_map fst _ _ He) as H1; rewrite mbio_ent_fst in H1.
    - apply NQL. apply in_or_app; left. apply in_or_app; right. exact H1.
    - apply (DJX _ H1). right. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  assert (NYL : forall e, In e (mbio_ent KY 0) -> ~ In e ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros e He [<-|X]; pose proof (in_map fst _ _ He) as H1; rewrite mbio_ent_fst in H1.
    - apply NQL. apply in_or_app; left. apply in_or_app; left. exact H1.
    - apply (DJY _ H1). apply in_or_app; right. right. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  assert (NEL : ~ In (e_E RT en, 904) ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))).
  { intros [X|X]; [injection X; intros _ EE; apply NQL; apply in_or_app; right; left; exact (eq_sym EE)|].
    apply NQE. pose proof (in_map fst _ _ X) as H2. rewrite mbio_ent_fst in H2. exact H2. }
  pose proof (com_WB_ok RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ5 m6 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4 - 1) _ ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en)) COM6
                ltac:(intros e [<-|He]; [left; split; [exact HLB| cbn; clear; lia]| right; exact He])) as (HWS & HWFR & HWFF & HWF & HWL & HWP).
  set (W := map rng ((LB1, 256) :: mbio_ent (e_K RT en) (e_bmax RT en))) in *.
  assert (OUTX : forall e x, In e (mbio_ent KX 0) -> fst e <= x < fst e + snd e -> outside W x).
  { intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ5 m6 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4 - 1) _ _ W COM6 HWL e x ltac:(right; apply in_or_app; right; apply in_or_app; left; exact He) (NXL _ He) Hx). }
  assert (OUTY : forall e x, In e (mbio_ent KY 0) -> fst e <= x < fst e + snd e -> outside W x).
  { intros e x He Hx. exact (com_cur_outX RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ5 m6 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4 - 1) _ _ W COM6 HWL e x ltac:(right; apply in_or_app; left; exact He) (NYL _ He) Hx). }
  assert (OUTE : forall x, e_E RT en <= x < e_E RT en + 904 -> outside W x).
  { intros x Hx. exact (HWL (e_E RT en) 904 x (ELV6 _ INE) NEL Hx). }
  assert (INF5 : In (e_f RT en, 1%nat) (rt_frames RT Σ5)) by (rewrite FRS5, FRS3, FRS2; exact INF).
  assert (LNJ' : length junk = 256%nat) by (rewrite LNJ; reflexivity).
  (* [comment removed for export] *)
  eapply (pem_call_bgets RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS C_BG T en Σ5 m6 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4 - 1) _ LB1 junk SITE_jn_gets
            F5 fc5 y0 y1 y2 d3 d4 d5 d6 d7 (wz (e_f RT en)) (wz BIy) (wz (e_flags RT en)) (wz LB1) (wz (e_f RT en)) (wz BIx) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 c7
            COM6 HLB AL16 LNJ' LBC6 ltac:(clear - CR3; lia) ltac:(unfold SITE_jn_gets; clear; lia) ltac:(reflexivity) Hc7').
  clear Hc7' y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6.
  intros Σ7 m7 F7 fc7 y0 y1 y2 b1 b2 b3 d4 d5 d6 d7 y3 y4 y5 y6 c8 k off' bs' COM7 LV7 FRS7 PR LBS7 LBC7 ARMS Hc8.
  pose proof COM7 as (ART7 & MI7 & _).
  change ((LB1, LB1 + 256) :: mbio_W (e_K RT en) (e_bmax RT en)) with W in PR.
  (* [comment removed for export] *)
  assert (REST7 : errst_at_rest (e_E RT en) [] m7).
  { eapply (rest_keep_n RT libenv errst_at_rest errst_fp errst_rest_agree errst_fp_where FZ_SITES FZ_CALLS en Σ5 m6 m7); [exact COM6| exact ER6| exact PR| rewrite LV7; exact (ELV6 _ INE)| exact OUTE]. }
  assert (PFR7 : pem_frame en m7 j0 lH lF endv BIx BIy x1 x2 gap) by exact (pem_frame_keep RT en m6 m7 _ _ _ j0 lH lF endv BIx BIy x1 x2 gap PFR6 PR PD TOP HWS).
  assert (FFC7 : rw_cells asegs m7 (e_f RT en) (ff_cells hj lenv j1 tav j2 bmv j3)) by exact (ff_keep m6 m7 (e_f RT en) _ _ _ _ hj lenv j1 tav j2 bmv j3 FFC6 PR INF5 HWFF).
  assert (ON7 : out_null RT en m7).
  { destruct ON6 as (O1 & O2 & O3 & O4). pose proof (com_out_agree RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ5 m6 m7 (e_boff RT en) (crem - 1 - 1) (lrem - 4 - 4 - 1) _ _ _ COM6 HWS HWFR PR) as AGP.
    assert (G8 : forall P vv, In P [e_PN RT en; e_PH RT en; e_PD RT en; e_PLN RT en] -> rw_cells asegs m6 P [C8 vv] -> rw_cells asegs m7 P [C8 vv]).
    { intros P vv HPP C. eapply rw_cells_agree_nw; [exact C|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact (AGP P HPP). }
    split; [apply G8; [cbn; tauto| exact O1]|]. split; [apply G8; [cbn; tauto| exact O2]|]. split; [apply G8; [cbn; tauto| exact O3]|]. apply G8; [cbn; tauto| exact O4]. }
  assert (MBX7 : mbio_rep (rt_live RT Σ7) m7 KX BIx meth 0 0 0).
  { eapply (mbio_rep_keep (rt_live RT Σ5)); [exact MBX6| exact PR| intros e He; rewrite LV7; split; apply CLV6; right; apply in_or_app; right; apply in_or_app; left; exact He| exact OUTX]. }
  assert (MBY7 : mbio_rep (rt_live RT Σ7) m7 KY BIy meth 0 0 0).
  { eapply (mbio_rep_keep (rt_live RT Σ5)); [exact MBY6| exact PR| intros e He; rewrite LV7; split; apply CLV6; right; apply in_or_app; left; exact He| exact OUTY]. }
  (* [comment removed for export] *)
  assert (COM7' : pem_com en Σ7 m7 off' (crem - 1 - 1 - 1) (lrem - 4 - 4 - 1) (mbio_ent KX 0 ++ mbio_ent KY 0 ++ [(LB1, 256)])).
  { eapply (com_perm RT libenv FZ_SITES FZ_CALLS en Σ7 m7); [exact COM7|]. rewrite app_nil_r.
    apply (Permutation_trans (l' := (LB1, 256) :: mbio_ent KX 0 ++ mbio_ent KY 0)); [apply perm_skip; apply Permutation_app_comm|].
    rewrite app_assoc. apply Permutation_cons_append. }
  clear COM6 COM7 ER6 PFR6 FFC6 ON6 MBX6 MBY6 LBC6 HWS HWFR HWFF HWF HWL HWP OUTX OUTY OUTE NXL NYL NEL.
  destruct ARMS as [(-> & -> & OFE)|(KR & NULk & LFk & ->)].
  - (* [comment removed for export] *)
    pose proof (jn4_walk_zero (wz SITE_jn_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) (wz (e_sp1 RT en)) b1 b2 b3 d4 d5 d6 d7 (wz (e_f RT en)) (wz BIy) (wz (e_flags RT en)) (wz LB1)
                  (wz (e_f RT en)) (wz BIx) (wz (shad (e_f RT en))) (wz SHB) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 F7 fc7 m7 MI7) as W4w.
    cl_lift W4w Hc8 c9 Hc9. destruct (ASTA_unpack RT Σ7 _ _ c9 Hc9) as (ms9 & (-> & _) & Hc9'). clear Hc9 Hc8.
    refine (H_R1 en Σ7 m7 (e_boff RT en) (crem - 1 - 1 - 1) (lrem - 4 - 4 - 1) j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F7 fc7 (wz SITE_jn_gets) y0 y1 y2 (wz 0) b1 b2 b3 d4 d5 d6 d7
              (wz (e_f RT en)) (wz BIy) (wz (e_flags RT en)) (wz (e_f RT en)) (wz BIx) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 LB1 BIx BIy bs' KX KY meth meth 0 0 0 0
              COM7' REST7 _ ltac:(clear - LRM; lia) PFR7 FFC7 ON7 AL16 LBS7 LBC7 MBX7 MBY7 T c9 Hc9' Hk).
    clear - CRM OFF BLT G255. unfold gn_need, C_END, grow_pot, grow_cap, e_plen in *. pose proof (gr_n_gt (2 * (e_blen RT en - e_boff RT en) + 8) ltac:(lia)) as G1. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    pose proof (jn4_walk_pos (wz SITE_jn_gets) (e_sp1 RT en) (e_gp RT en) y0 y1 y2 (e_sp RT en) (wz (e_sp1 RT en)) k b1 b2 b3 d4 d5 d6 d7 (wz (e_f RT en)) (wz BIy) (wz (e_flags RT en)) (wz LB1)
                  (wz (e_f RT en)) (wz BIx) (wz (shad (e_f RT en))) (wz SHB) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 F7 fc7 m7 ltac:(clear - KR; lia) MI7) as W4w.
    cl_lift W4w Hc8 c9 Hc9. destruct (ASTA_unpack RT Σ7 _ _ c9 Hc9) as (ms9 & (-> & _) & Hc9'). clear Hc9 Hc8.
    refine (H_J0G en Σ7 m7 (e_boff RT en + k) (crem - 1 - 1 - 1) (lrem - 4 - 4 - 1) j0 lH lF endv x1 x2 gap hj lenv j1 tav j2 bmv j3 F7 fc7 (wz SITE_jn_gets) y0 y1 y2 b1 b2 b3 d4 d5 d6 d7
              (wz (e_f RT en)) (wz (e_flags RT en)) (wz (e_f RT en)) (wz (e_PD RT en)) (wz (e_PH RT en)) y3 y4 y5 y6 LB1 BIx BIy k bs' KX KY meth meth 0 0
              COM7' REST7 _ ltac:(clear - LRM; lia) PFR7 FFC7 ON7 AL16 LBS7 LBC7 ltac:(clear - KR; lia) NULk MBX7 MBY7 eq_refl eq_refl T c9 Hc9' Hk).
    clear - CRM OFF BLT G255 KR. unfold gn_need, C_END, grow_pot, grow_cap, e_plen in *. pose proof (gr_n_gt (2 * (e_blen RT en - e_boff RT en) + 8) ltac:(lia)) as G1. pose proof (gr_n_gt (2 * (e_blen RT en - (e_boff RT en + k)) + 8) ltac:(lia)) as G2. Z.div_mod_to_equations. nia.
Qed.
End CJ0n.
