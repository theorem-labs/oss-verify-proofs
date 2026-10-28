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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex Th_mutex_init I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_locknew Fz_M_strdup Fz_W5_icb Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tslia ::= wp_tslia.
Notation TP_A := (0xba3ef0)%Z (only parsing).
Local Ltac zgo p := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lfix
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ifF | ifT | ubs_if] end).
Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

Definition e_rand_ctx_new : Z := 0x253870.
Definition SITE_rcx_zalloc : Z := 0x2538b0.     (* [comment removed for export] *)
Definition SITE_rcx_icb : Z := 0x2538c4.        (* [comment removed for export] *)
Definition SITE_rcx_strdup : Z := 0x2538dc.     (* [comment removed for export] *)
Definition SITE_rcx_locknew : Z := 0x2538fc.    (* [comment removed for export] *)
Definition RCX_FILE : Z := 0x73bc0.             (* [comment removed for export] *)
Definition STR_FIPS : Z := 0x73c60.             (* [comment removed for export] *)
Definition FIPS : list byte := [Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 112; Z_to_bv 8 115].
(* [comment removed for export] *)
Definition rcx_cells (lk q : Z) : list cell :=
  [C8 (Z_to_bv 64 lk); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 q); CB 48 (repeat (Z_to_bv 8 0) 48)].

(* [comment removed for export] *)
Definition rcx_w0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_rcx_zalloc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 88) (Z_to_bv 64 RCX_FILE) (Z_to_bv 64 449)
                 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma rcx_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (rcx_w0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_rand_ctx_new) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC MI. unfold e_rand_ctx_new, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia.
  carve_frame 48%nat ST.
  zgo 0x1fbfec.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold rcx_w0_post, SITE_rcx_zalloc, RCX_FILE, e_CRYPTO_zalloc. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR| exact ST].
Qed.

(* [comment removed for export] *)
Lemma rcx_w1 : forall sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (p : Z),
  0 < p -> p < 2^64 ->
  evt asegs (eq (MS (mkR (Z_to_bv 64 SITE_rcx_icb) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 OPT_BASE_ONLY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_init_crypto) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 SITE_rcx_zalloc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcx_zalloc) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros P0 PH. unfold SITE_rcx_zalloc.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  zgo 0x1f3600.
  unfold SITE_rcx_icb, OPT_BASE_ONLY, e_init_crypto. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rcx_w2 : forall sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  evt asegs (eq (MS (mkR (Z_to_bv 64 SITE_rcx_strdup) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STR_FIPS) (Z_to_bv 64 RCX_FILE) (Z_to_bv 64 462) a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_CRYPTO_strdup) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 SITE_rcx_icb) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcx_icb) fc None m (seg_rom asegs)).
Proof.
  intros. unfold SITE_rcx_icb.
  zgo 0x202ecc.
  unfold SITE_rcx_strdup, STR_FIPS, RCX_FILE, e_CRYPTO_strdup. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rcx_w3_post (sp gp tp t0 t1 t2 s0 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p q : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_rcx_locknew) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (p + 32)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (Z.shiftr (p + 32) 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_lock_new) fc None m' (seg_rom asegs)
    /\ munch [(p + 32, p + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' p [CB 32 (repeat (Z_to_bv 8 0) 32); C8 (Z_to_bv 64 q); CB 48 (repeat (Z_to_bv 8 0) 48)].

Lemma rcx_w3 : forall sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (p q : Z),
  0x10007fff8000 <= p -> p + 88 <= 2^47 -> p mod 8 = 0 -> 0 < q -> q < 2^64 ->
  rw_cells asegs m p [CB 32 (repeat (Z_to_bv 8 0) 32); C8 (Z_to_bv 64 0); CB 48 (repeat (Z_to_bv 8 0) 48)] -> acc asegs m p 88 -> mem_inv asegs m ->
  evt asegs (rcx_w3_post sp gp tp t0 t1 t2 s0 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p q m)
    (MS (mkR (Z_to_bv 64 SITE_rcx_strdup) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcx_strdup) fc None m (seg_rom asegs)).
Proof.
  intros until q. intros PH PT PA Q0 QH HP ACp MI. unfold SITE_rcx_strdup in *.
  pose proof (munch_refl [(p + 32, p + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zgo 0x2538ec. zsh.
  zgo 0x1f5e3c.
  unfold rcx_w3_post, SITE_rcx_locknew, e_lock_new. apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption| exact HP].
Qed.

(* [comment removed for export] *)
Definition rcx_w4_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p q lk lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 p) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(p, p + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' p (rcx_cells lk q).

Lemma rcx_w4 : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (s0' s1' s2' s3' s4' : word)
    (F : bvmap 5 word) fc (m : mem) (p q lk lo : Z),
  lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0x10007fff8000 <= p -> p + 88 <= 2^47 -> p mod 8 = 0 -> p + 88 <= lo -> 0 < lk -> lk < 2^64 ->
  stk asegs m lo (bv_unsigned sp + -48) ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m p [C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 q); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
  acc asegs m p 88 -> mem_inv asegs m ->
  evt asegs (rcx_w4_post ra0 sp gp tp s0' s1' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc p q lk lo m)
    (MS (mkR (Z_to_bv 64 SITE_rcx_locknew) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 p) (Z_to_bv 64 lk) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rcx_locknew) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH PH PT PA PSTK LK0 LKH ST FR HP ACp MI. unfold SITE_rcx_locknew in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(p, p + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 lk) = lk) by (apply unsigned_lit; lia).
  zgo 0x253908. zsh.
  zgo 0x253968.
  release_frame FR ST SP.
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold rcx_w4_post, rcx_cells. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact ST| exact HP].
Qed.

Lemma rcx_rw_of_bytes : forall (m : mem) a bs, bytes_at asegs m a bs -> wr_at asegs m a (Z.of_nat (length bs)) -> rw_cells asegs m a [CB (length bs) bs].
Proof.
  intros m a bs BA WR. split.
  - split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact WR.
Qed.

(* [comment removed for export] *)
Lemma fips_ro_bytes : ro_bytes asegs STR_FIPS (FIPS ++ Z_to_bv 8 0 :: [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition RCX_COST : Z := mcost 88 + 1 + mcost 5 + 1.
Lemma RCX_COST_nonneg : 0 <= RCX_COST.
Proof. unfold RCX_COST. pose proof (wg_mcost_nonneg 88). pose proof (wg_mcost_nonneg 5). lia. Qed.

Section RandCtxNew.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_ICB : init_crypto_base_stmt RT.
Hypothesis C_SD : crypto_strdup_env_stmt RT GOBJ.
Hypothesis C_LN : crypto_lock_new_env_stmt RT.
Hypothesis GO_fips : GOBJ STR_FIPS 5.

Definition RCX_SITES : list (Z * Z) :=
  [(SITE_rcx_zalloc, e_rand_ctx_new); (SITE_rcx_strdup, e_rand_ctx_new); (SITE_rcx_locknew, e_rand_ctx_new);
   (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_sd_malloc, e_CRYPTO_strdup); (SITE_ln_zalloc, e_lock_new)].
Definition RCX_CALLS : list (Z * Z) :=
  [(SITE_rcx_zalloc, e_CRYPTO_zalloc); (SITE_rcx_strdup, e_CRYPTO_strdup); (SITE_rcx_locknew, e_lock_new);
   (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_sd_malloc, e_CRYPTO_malloc); (SITE_ln_zalloc, e_CRYPTO_zalloc)].

(* [comment removed for export] *)
Definition rand_ctx_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (od : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x230 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_rand_ctx_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) RCX_SITES RCX_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 3 <= LIVE_MAX -> RCX_COST <= rt_credit RT Σ ->
  cl_env m lb canary ->
  rw_cells asegs m 0xb9f200 [C1 (Z_to_bv 8 0)] -> rw_cells asegs m 0xb9f2a0 [C8 od] ->
  rw_cells asegs m 0xb9f2c0 [C4 (Z_to_bv 64 2)] -> rw_cells asegs m 0xb9f2e0 [C4 (Z_to_bv 64 1)] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_rand_ctx_new m)))
    (fun c => exists (Σ' : rts RT) (p q lk : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' p 88 /\ acc asegs m' p 88
           /\ rw_cells asegs m' p (rcx_cells lk q)
           /\ rw_cells asegs m' q [C1 (Z_to_bv 8 102); C1 (Z_to_bv 8 105); C1 (Z_to_bv 8 112); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 0)]
           /\ rw_cells asegs m' lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' 0xb9f200 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' 0xb9f2a0 [C8 od]
           /\ rw_cells asegs m' 0xb9f2c0 [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' 0xb9f2e0 [C4 (Z_to_bv 64 1)]) c
       /\ rt_live RT Σ' = (lk, 40) :: (q, 5) :: (p, 88) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - RCX_COST
       /\ 0 < p /\ p mod 16 = 0 /\ p + 88 < USTACK_TOP /\ 0 < q /\ q mod 16 = 0 /\ q + 5 < USTACK_TOP /\ 0 < lk /\ lk mod 16 = 0 /\ lk + 40 < USTACK_TOP
       /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem rand_ctx_new_cps : rand_ctx_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary od
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV XS0 XS1 XS2 XS3.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ usp <= 2^47) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -48).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  unfold RCX_COST in Hcr. pose proof (wg_mcost_nonneg 88) as MC1. pose proof (wg_mcost_nonneg 5) as MC2.
  (* [comment removed for export] *)
  assert (STAT : forall (mA mB : mem) a cs, rw_cells asegs mA a cs -> wmono asegs mA mB -> 0xb9f200 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f400 ->
                 (forall x : word, 0xb9f200 <= bv_unsigned x < 0xb9f400 -> mB x = mA x) -> rw_cells asegs mB a cs).
  { intros mA mB a cs H WM H1 H2 AG. apply (rw_cells_agree asegs mA mB _ _ H); [| exact WM]. intros x Hx. apply AG. clear - Hx H1 H2. lia. }
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in XS0, XS1, XS2, XS3 |- *.
  (* [comment removed for export] *)
  pose proof (rcx_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(lia) ltac:(lia) UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  assert (SAG1 : forall x : word, 0xb9f200 <= bv_unsigned x < 0xb9f400 -> m1 x = m x) by (intros x Hx; apply MU1; cbn [outside]; clear - Hx NUM HSTK; unfold RT_STACK in *; split; [lia | exact I]).
  pose proof (STAT m m1 _ _ XS0 WM1 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG1) as XS0_1. pose proof (STAT m m1 _ _ XS1 WM1 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG1) as XS1_1.
  pose proof (STAT m m1 _ _ XS2 WM1 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG1) as XS2_1. pose proof (STAT m m1 _ _ XS3 WM1 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG1) as XS3_1.
  destruct (cl_chain_call (rt_cg RT Σ) e_rand_ctx_new e_CRYPTO_zalloc SITE_rcx_zalloc m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWC AG1
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_CZ Σ PMc (Z_to_bv 64 SITE_rcx_zalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp s1 (Z_to_bv 64 88) (Z_to_bv 64 RCX_FILE) (Z_to_bv 64 449)
           a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 88 lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl ltac:(clear; lia) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. clear - HSTK. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_rcx_zalloc) by (unfold SITE_rcx_zalloc; lia). exact CTXc1. }
  { exact UWCc1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { clear - Hlen. lia. }
  { clear - Hcr MC1 MC2. lia. }
  { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ENV2 & WRp2 & ACCp2 & ZERp2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_rcx_zalloc) in Hc2' by (unfold SITE_rcx_zalloc; lia).
  assert (INP1 : In (p, 88) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 p 88 ART2 INP1 ltac:(lia)) as PHH.
  pose proof (af_live_range RT AF Σ1 m2 p 88 ART2 INP1) as (_ & PLO & _). rewrite SP1 in PLO.
  pose proof (wg_mod16_8 _ P16) as PAL.
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; clear - H1 H2 Hx; lia |].
    cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H1 Hx NUM HSTK. unfold usp1, USTACK_TOP, RT_STACK in *. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (AG12u : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; cbv beta in Ha; apply PRES2; [left; unfold usp1; lia | cbn [outside]; unfold G_ALLOW_CUST, USTACK_TOP in *; split; [lia | exact I]]).
  pose proof (uw_chain_agree outer m1 m2 sp s0 ltac:(exact (uw_chain_agree outer m m1 sp s0 UWC AG1)) AG12u) as UWF2.
  assert (SAG2 : forall x : word, 0xb9f200 <= bv_unsigned x < 0xb9f400 -> m2 x = m1 x).
  { intros x Hx. apply PRES2; [right; left; apply client_static_intro; clear - Hx; lia | cbn [outside]; unfold G_ALLOW_CUST; clear - Hx; split; [lia | exact I]]. }
  pose proof (STAT m1 m2 _ _ XS0_1 WM2 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG2) as XS0_2. pose proof (STAT m1 m2 _ _ XS1_1 WM2 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG2) as XS1_2.
  pose proof (STAT m1 m2 _ _ XS2_1 WM2 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG2) as XS2_2. pose proof (STAT m1 m2 _ _ XS3_1 WM2 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG2) as XS3_2.
  (* [comment removed for export] *)
  pose proof (rcx_w1 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp s1 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 p
                P0 ltac:(clear - PU; unfold USTACK_TOP in *; lia)) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  (* [comment removed for export] *)
  apply (C_ICB Σ1 PMc (Z_to_bv 64 SITE_rcx_icb) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 p) (Z_to_bv 64 OPT_BASE_ONLY) (Z_to_bv 64 0)
           b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo od FDO MST eq_refl eq_refl ART2 MI2).
  { fold usp in SPA. cl_call_ok EU1 ST2 LOW1 SPA 3. }
  { rewrite EU1. clear - HSTK. unfold usp1, RT_STACK in *. lia. }
  { rewrite FRS1. exact Hfr. }
  { rewrite CR1. clear - Hcr MC1 MC2. lia. }
  { exact XS0_2. }
  { exact XS1_2. }
  { exact XS2_2. }
  { exact XS3_2. }
  { exact Hc3. }
  clear Hc3. intros c4 (Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m3 & RS4 & (ART3 & MI3 & WM3 & ST3) & PRES3 & XS0_3 & XS1_3 & XS2_3 & XS3_3) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & c_1 & c_2 & c_3 & c_4 & c_5 & c_6 & c_7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite (ret_pc_even SITE_rcx_icb) in Hc4' by (unfold SITE_rcx_icb; lia).
  assert (INP2 : In (p, 88) (rt_live RT Σ2)) by (rewrite LV2; exact INP1).
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW1).
  assert (AG3 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES3. left. clear - H1 H2 Hx. lia. }
  cl_keep FR2 AG3 WM3 FR3.
  assert (AG23u : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; cbv beta in Ha; apply PRES3; left; unfold usp1; lia).
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWF2 AG23u) as UWF3.
  assert (ENV3 : cl_env m3 (Z_to_bv 8 1) canary) by exact (cl_env_pres _ _ _ m2 m3 _ canary ENV2 PRES3).
  assert (ZERp3 : bytes_at asegs m3 p (repeat (Z_to_bv 8 0) (Z.to_nat 88))).
  { apply (bytes_at_agree asegs m2 m3 _ _ ZERp2). intros x Hx. apply PRES3. apply (acl_live _ _ _ p 88); [exact INP1 | rewrite repeat_length in Hx; clear - Hx; lia]. }
  (* [comment removed for export] *)
  pose proof (rcx_w2 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) v0 v1 v2 sp (Z_to_bv 64 p) (Z_to_bv 64 1) c_1 c_2 c_3 c_4 c_5 c_6 c_7 s2 (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11
                v3 v4 v5 v6 F3 fc3 m3) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (cl_chain_call (rt_cg RT Σ2) e_rand_ctx_new e_CRYPTO_strdup SITE_rcx_strdup m3 m3 ra s0 sp (Z_to_bv 64 usp1) outer ltac:(rewrite CG2, CG1; exact CTX)
              ltac:(rewrite CG2, CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG2, CG1; apply (proj2 CGH); wp_in_lit) UWF3 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m3 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR3))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTXc3 & UWCc3).
  assert (NOZ : ~ In (Z_to_bv 8 0) FIPS).
  { unfold FIPS. cbn [In]. intros [H|[H|[H|[H|[]]]]]; apply (f_equal bv_unsigned) in H; vm_compute in H; clear - H; lia. }
  (* [comment removed for export] *)
  apply (C_SD Σ2 PMc (Z_to_bv 64 SITE_rcx_strdup) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) v0 v1 v2 sp (Z_to_bv 64 p) (Z_to_bv 64 STR_FIPS) (Z_to_bv 64 RCX_FILE) (Z_to_bv 64 462)
           c_3 c_4 c_5 c_6 c_7 s2 (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m3 STR_FIPS STR_FIPS 5 FIPS [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
           lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl fips_ro_bytes NOZ ltac:(cbn; clear; lia) ltac:(vm_compute; discriminate)
           GO_fips ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(unfold STR_FIPS; clear; lia) ltac:(unfold STR_FIPS, SEGTOP_A; cbn; clear; lia) ART3 MI3).
  { fold usp in SPA. cl_call_ok EU1 ST3 LOW2 SPA 3. }
  { rewrite EU1. clear - HSTK. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_rcx_strdup) by (unfold SITE_rcx_strdup; lia). exact CTXc3. }
  { exact UWCc3. }
  { rewrite CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV2, LV1. cbn [length]. clear - Hlen. lia. }
  { rewrite CR2, CR1. change (Z.of_nat (length FIPS) + 1) with 5. clear - Hcr MC1 MC2. lia. }
  { exact ENV3. }
  { exact Hc5. }
  clear Hc5. intros c6 (Σ3 & q & Hc6 & LV3 & FRS3 & SP3 & CR3 & Q0 & Q16 & QU & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m4 & RS6 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ENV4 & WRq4 & ACCq4 & BAq4) & Hc6'). clear Hc6.
  destruct RS6 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_rcx_strdup) in Hc6' by (unfold SITE_rcx_strdup; lia).
  change (Z.of_nat (length FIPS) + 1) with 5 in LV3, CR3, QU, WRq4, ACCq4.
  assert (INP3 : In (p, 88) (rt_live RT Σ3)) by (rewrite LV3; right; exact INP2).
  assert (INQ3 : In (q, 5) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
  assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP3; exact LOW2).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m4 q 5 ART4 INQ3 ltac:(lia)) as QHH.
  pose proof (af_live_range RT AF Σ3 m4 q 5 ART4 INQ3) as (_ & QLO & _). rewrite SP3, SP2, SP1 in QLO.
  pose proof (af_live_disj RT AF Σ3 m4 q 5 p 88 [] (rt_live RT Σ2) ART4 LV3 INP2) as QP. wp_box1 QP.
  assert (AG4 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; clear - H1 H2 Hx; lia |].
    cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H1 Hx NUM HSTK. unfold usp1, USTACK_TOP, RT_STACK in *. lia. }
  cl_keep FR3 AG4 WM4 FR4.
  assert (AG34u : agree_on (fun x => usp <= x < USTACK_TOP) m3 m4) by (intros a Ha; cbv beta in Ha; apply PRES4; [left; unfold usp1; lia | cbn [outside]; unfold G_ALLOW_CUST, USTACK_TOP in *; split; [lia | exact I]]).
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWF3 AG34u) as UWF4.
  assert (SAG4 : forall x : word, 0xb9f200 <= bv_unsigned x < 0xb9f400 -> m4 x = m3 x).
  { intros x Hx. apply PRES4; [right; left; apply client_static_intro; clear - Hx; lia | cbn [outside]; unfold G_ALLOW_CUST; clear - Hx; split; [lia | exact I]]. }
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in XS0_3, XS1_3, XS2_3, XS3_3.
  pose proof (STAT m3 m4 _ _ XS0_3 WM4 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG4) as XS0_4. pose proof (STAT m3 m4 _ _ XS1_3 WM4 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG4) as XS1_4.
  pose proof (STAT m3 m4 _ _ XS2_3 WM4 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG4) as XS2_4. pose proof (STAT m3 m4 _ _ XS3_3 WM4 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG4) as XS3_4.
  (* [comment removed for export] *)
  assert (ZERp4 : bytes_at asegs m4 p (repeat (Z_to_bv 8 0) (Z.to_nat 88))).
  { apply (bytes_at_agree asegs m3 m4 _ _ ZERp3). intros x Hx. rewrite repeat_length in Hx. apply PRES4; [apply (acl_live _ _ _ p 88); [exact INP2 | clear - Hx; lia] |].
    cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - Hx PHH. lia. }
  pose proof (af_acc_live RT AF Σ3 m4 p 88 ART4 INP3) as (WRp4 & ACCp4).
  assert (HP4 : rw_cells asegs m4 p [CB 32 (repeat (Z_to_bv 8 0) 32); C8 (Z_to_bv 64 0); CB 48 (repeat (Z_to_bv 8 0) 48)]).
  { pose proof (wp_zero_rw_CB asegs m4 p 88 ZERp4 WRp4 ltac:(lia)) as HZ. change (Z.to_nat 88) with 88%nat in HZ.
    apply (rw_cells_recast m4 p _ _ HZ); [cbn; repeat first [exact I | reflexivity | split] | reflexivity]. }
  assert (HQ4 : rw_cells asegs m4 q [C1 (Z_to_bv 8 102); C1 (Z_to_bv 8 105); C1 (Z_to_bv 8 112); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 0)]).
  { pose proof (rcx_rw_of_bytes m4 q _ BAq4 WRq4) as HB.
    apply (rw_cells_recast m4 q _ _ HB); [cbn; repeat first [exact I | reflexivity | split] | reflexivity]. }
  (* [comment removed for export] *)
  pose proof (rcx_w3 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp d1 d2 d3 d4 d5 d6 d7 s2 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 p q
                PHH ltac:(clear - PU; unfold USTACK_TOP in *; lia) PAL Q0 ltac:(clear - QU; unfold USTACK_TOP in *; lia) HP4 ACCp4 MI4) as W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (m5 & -> & MU5 & WM5 & MI5 & HP5) & Hc7'). clear Hc7.
  assert (ART5 : ART RT Σ3 m5).
  { apply (af_frame RT AF Σ3 m4 m5 usp1 ART4 ltac:(rewrite SP3, SP2, SP1; clear - NUM; unfold usp1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ p 88); [exact INP3 | clear - Hin; lia]. }
  pose proof (cl_env_seg _ m4 m5 _ canary ENV4 MU5 ltac:(cl_fp_lia)) as ENV5.
  assert (AG45 : forall a k, (a + k <= p + 32 \/ p + 40 <= a) -> agree_on (fun x => a <= x < a + k) m4 m5).
  { intros a k H. apply (agree_of_munch _ m4 m5 _ MU5). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (ST5 : stk asegs m5 lo usp1).
  { apply (stk_munch _ m4 m5 _ _ ST4 MU5 WM5). intros x Hx. cbn [outside]. clear - Hx PLO LOW HSTK. unfold usp1, RT_STACK in *. lia. }
  assert (FR5 : rw_cells asegs m5 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m5 _ _ FR4); [| exact WM5]. apply AG45. cbn [cells_size csize Nat.add]. clear - PLO LOW HSTK. unfold RT_STACK in *. lia. }
  assert (HQ5 : rw_cells asegs m5 q [C1 (Z_to_bv 8 102); C1 (Z_to_bv 8 105); C1 (Z_to_bv 8 112); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_agree asegs m4 m5 _ _ HQ4); [| exact WM5]. apply AG45. cbn [cells_size csize Nat.add]. unfold wp_box in QP. clear - QP. lia. }
  assert (SAG5 : forall x : word, 0xb9f200 <= bv_unsigned x < 0xb9f400 -> m5 x = m4 x).
  { intros x Hx. apply MU5. cbn [outside]. clear - Hx PHH. split; [lia | exact I]. }
  pose proof (STAT m4 m5 _ _ XS0_4 WM5 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG5) as XS0_5. pose proof (STAT m4 m5 _ _ XS1_4 WM5 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG5) as XS1_5.
  pose proof (STAT m4 m5 _ _ XS2_4 WM5 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG5) as XS2_5. pose proof (STAT m4 m5 _ _ XS3_4 WM5 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG5) as XS3_5.
  assert (AG45u : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5).
  { replace USTACK_TOP with (usp + (USTACK_TOP - usp)) by lia. apply AG45. clear - PLO LOW HSTK. unfold RT_STACK in *. lia. }
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWF4 AG45u) as UWF5.
  destruct (cl_chain_call (rt_cg RT Σ3) e_rand_ctx_new e_lock_new SITE_rcx_locknew m5 m5 ra s0 sp (Z_to_bv 64 usp1) outer ltac:(rewrite CG3, CG2, CG1; exact CTX)
              ltac:(rewrite CG3, CG2, CG1; apply (proj1 CGH); wp_in_lit) ltac:(rewrite CG3, CG2, CG1; apply (proj2 CGH); wp_in_lit) UWF5 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m5 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR5))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTXc5 & UWCc5).
  (* [comment removed for export] *)
  apply (C_LN Σ3 PMc (Z_to_bv 64 SITE_rcx_locknew) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 0) d2 d3 d4 d5 d6 d7
           (Z_to_bv 64 (p + 32)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (Z.shiftr (p + 32) 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m5
           lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART5 MI5).
  { fold usp in SPA. cl_call_ok EU1 ST5 LOW3 SPA 3. }
  { rewrite EU1. clear - HSTK. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_rcx_locknew) by (unfold SITE_rcx_locknew; lia). exact CTXc5. }
  { exact UWCc5. }
  { rewrite CG3, CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS3, FRS2, FRS1. exact Hfr. }
  { rewrite LV3, LV2, LV1. cbn [length]. clear - Hlen. lia. }
  { rewrite CR3, CR2, CR1. clear - Hcr MC1 MC2. lia. }
  { exact ENV5. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ4 & lk & Hc8 & LV4 & FRS4 & SP4 & CR4 & LK0 & LK16 & LKU & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c8 Hc8) as (ms8 & (m6 & RS8 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ENV6 & HLK6 & ACClk6) & Hc8'). clear Hc8.
  destruct RS8 as (x0 & x1 & x2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_rcx_locknew) in Hc8' by (unfold SITE_rcx_locknew; lia).
  assert (INP4 : In (p, 88) (rt_live RT Σ4)) by (rewrite LV4; right; exact INP3).
  assert (INQ4 : In (q, 5) (rt_live RT Σ4)) by (rewrite LV4; right; exact INQ3).
  assert (INL4 : In (lk, 40) (rt_live RT Σ4)) by (rewrite LV4; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP Σ4 m6 lk 40 ART6 INL4 ltac:(lia)) as LHH.
  pose proof (af_live_disj RT AF Σ4 m6 lk 40 p 88 [] (rt_live RT Σ3) ART6 LV4 INP3) as LP. wp_box1 LP.
  assert (AG6 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES6; [left; clear - H1 H2 Hx; lia |].
    cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H1 Hx NUM HSTK. unfold usp1, USTACK_TOP, RT_STACK in *. lia. }
  cl_keep FR5 AG6 WM6 FR6.
  assert (SAG6 : forall x : word, 0xb9f200 <= bv_unsigned x < 0xb9f400 -> m6 x = m5 x).
  { intros x Hx. apply PRES6; [right; left; apply client_static_intro; clear - Hx; lia | cbn [outside]; unfold G_ALLOW_CUST; clear - Hx; split; [lia | exact I]]. }
  pose proof (STAT m5 m6 _ _ XS0_5 WM6 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG6) as XS0_6. pose proof (STAT m5 m6 _ _ XS1_5 WM6 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG6) as XS1_6.
  pose proof (STAT m5 m6 _ _ XS2_5 WM6 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG6) as XS2_6. pose proof (STAT m5 m6 _ _ XS3_5 WM6 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG6) as XS3_6.
  assert (HEAP6 : forall b n a k, In (b, n) (rt_live RT Σ3) -> n <= 64512 -> b <= a -> a + k <= b + n -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros b n a k Hin Hn H1 H2 x Hx. cbv beta in Hx. apply PRES6; [apply (acl_live _ _ _ b n); [exact Hin | clear - H1 H2 Hx; lia] |].
    pose proof (afp_live_hi RT GOBJ AFP Σ3 m5 b n ART5 Hin Hn) as BH. cbn [outside]. unfold G_ALLOW_CUST. split; [| exact I]. clear - H1 Hx BH. lia. }
  assert (HP6 : rw_cells asegs m6 p [C8 (Z_to_bv 64 0); CB 24 (repeat (Z_to_bv 8 0) 24); C8 (Z_to_bv 64 q); CB 48 (repeat (Z_to_bv 8 0) 48)]).
  { apply (rw_cells_recast m6 p [CB 32 (repeat (Z_to_bv 8 0) 32); C8 (Z_to_bv 64 q); CB 48 (repeat (Z_to_bv 8 0) 48)]); [| cbn; repeat first [exact I | reflexivity | split] | reflexivity].
    apply (rw_cells_agree asegs m5 m6 _ _ HP5); [| exact WM6]. apply (HEAP6 p 88 p _ INP3 ltac:(clear; lia) ltac:(clear; lia)). cbn [cells_size csize Nat.add]. clear; lia. }
  assert (HQ6 : rw_cells asegs m6 q [C1 (Z_to_bv 8 102); C1 (Z_to_bv 8 105); C1 (Z_to_bv 8 112); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_agree asegs m5 m6 _ _ HQ5); [| exact WM6]. apply (HEAP6 q 5 q _ INQ3 ltac:(clear; lia) ltac:(clear; lia)). cbn [cells_size csize Nat.add]. clear; lia. }
  pose proof (af_acc_live RT AF Σ4 m6 p 88 ART6 INP4) as (WRp6 & ACCp6).
  (* [comment removed for export] *)
  pose proof (rcx_w4 ra sp gp (Z_to_bv 64 TP_A) x0 x1 x2 g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 (p + 32)) (Z_to_bv 64 (Z.shiftr (p + 32) 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11
                x3 x4 x5 x6 s0 s1 s2 s3 s4 F6 fc6 m6 p q lk lo
                ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(lia) ltac:(lia) PHH ltac:(clear - PU; unfold USTACK_TOP in *; lia) PAL
                ltac:(clear - PLO LOW HSTK; unfold RT_STACK in *; lia) LK0 ltac:(clear - LKU; unfold USTACK_TOP in *; lia) ST6 FR6 HP6 ACCp6 MI6) as W4.
  fold usp in W4.
  cl_lift W4 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ4 _ _ c9 Hc9) as (ms9 & (m7 & -> & MU7 & WM7 & MI7 & ST7 & HP7) & Hc9'). clear Hc9.
  fold usp in ST7, Hc9'.
  assert (ART7 : ART RT Σ4 m7).
  { apply (af_frame RT AF Σ4 m6 m7 usp1 ART6 ltac:(rewrite SP4, SP3, SP2, SP1; clear - NUM; unfold usp1; lia)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ p 88); [exact INP4 | clear - Hin; lia]. }
  assert (AG67 : forall a k, (a + k <= p \/ p + 8 <= a) -> agree_on (fun x => a <= x < a + k) m6 m7).
  { intros a k H. apply (agree_of_munch _ m6 m7 _ MU7). intros x Hx. cbv beta in Hx. cbn [outside]. clear - H Hx. lia. }
  assert (SAG7 : forall x : word, 0xb9f200 <= bv_unsigned x < 0xb9f400 -> m7 x = m6 x).
  { intros x Hx. apply MU7. cbn [outside]. clear - Hx PHH. split; [lia | exact I]. }
  (* [comment removed for export] *)
  apply Hk. exists Σ4, p, q, lk.
  split; [| split; [rewrite LV4, LV3, LV2, LV1; reflexivity | split; [rewrite FRS4, FRS3, FRS2, FRS1; reflexivity | split; [rewrite SP4, SP3, SP2, SP1; reflexivity
          | split; [rewrite CR4, CR3, CR2, CR1; unfold RCX_COST; clear; lia |]]]]].
  2: { repeat (split; [assumption|]). exact ltac:(rewrite CG4, CG3, CG2, CG1; reflexivity). }
  eapply ASTA_conseq; [exact Hc9'|]. intros ms <-. exists m7.
  split; [exists x0, x1, x2, (Z_to_bv 64 0), g2, g3, g4, g5, g6, g7, x3, x4, x5, x6, F6, fc6; reflexivity|].
  split; [split; [exact ART7 | split; [exact MI7 | split; [| exact ST7]]]|].
  { exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4
             (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 WM7)))))). }
  split.
  { intros a Ha Ho.
    assert (A0' : aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | clear; unfold usp1; lia]).
    assert (A1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A0'); [rewrite LV1; intros e He; right; exact He | rewrite FRS1; auto | clear; lia]).
    assert (A2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A1); [rewrite LV2; auto | rewrite FRS2; auto | clear; lia]).
    assert (A3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A2); [rewrite LV3; intros e He; right; exact He | rewrite FRS3; auto | clear; lia]).
    pose proof (newchunk_apart RT AF Σ Σ1 m2 p 88 usp _ ART2 LV1 FRS1 SP1 ltac:(clear - NUM; lia) ltac:(clear; lia) Ha) as Np.
    rewrite (MU7 a ltac:(cbn [outside]; split; [clear - Np; lia | exact I])).
    rewrite (PRES6 a A3 Ho).
    rewrite (MU5 a ltac:(cbn [outside]; split; [clear - Np; lia | exact I])).
    rewrite (PRES4 a A2 Ho).
    rewrite (PRES3 a A1).
    rewrite (PRES2 a A0' Ho).
    exact (PR1 a Ha I). }
  split; [exact (cl_env_seg _ m6 m7 _ canary ENV6 MU7 ltac:(cl_fp_lia))|].
  pose proof (af_acc_live RT AF Σ4 m7 p 88 ART7 INP4) as (WRp7 & ACCp7).
  split; [exact WRp7|]. split; [exact ACCp7|]. split; [exact HP7|].
  split; [apply (rw_cells_agree asegs m6 m7 _ _ HQ6); [| exact WM7]; apply AG67; cbn [cells_size csize Nat.add]; unfold wp_box in QP; clear - QP; lia|].
  split; [apply (rw_cells_agree asegs m6 m7 _ _ HLK6); [| exact WM7]; apply AG67; unfold mutex_cells; cbn [cells_size csize Nat.add]; unfold wp_box in LP; clear - LP; lia|].
  split; [exact (STAT m6 m7 _ _ XS0_6 WM7 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG7)|].
  split; [exact (STAT m6 m7 _ _ XS1_6 WM7 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG7)|].
  split; [exact (STAT m6 m7 _ _ XS2_6 WM7 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG7)|].
  exact (STAT m6 m7 _ _ XS3_6 WM7 ltac:(clear; lia) ltac:(cbn; clear; lia) SAG7).
Qed.
End RandCtxNew.
