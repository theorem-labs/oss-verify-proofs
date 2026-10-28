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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_free Fz_M_cleanse Fz_M_clear_free Fz_M_clear_realloc Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_secre Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Lemma gr_g2s_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BM D q n len max len' : Z) (flw : word) (j : list byte),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -80) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -80) (CB 8 j :: gr_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BM (bufmem_cells len D max flw) -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 <= lo ->
  0 < q -> q + n < 2^63 -> 0 <= n -> 0 <= len <= len' -> len' < 2^40 -> 0 <= D < 2^64 -> 0 <= max < 2^64 -> mem_inv asegs m ->
  evt asegs (gr_g2_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' BM q n len len' lo flw j m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 len') (Z_to_bv 64 q) a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_gr_secre) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT SHC FR BMC ACCBM BM0 BMAL BMHI BMLO Q0 QHI HN HLEN HL40 HD HMAX MI.
  unfold SITE_gr_secre, g_shadow_memory_dynamic_address, bufmem_cells, gr_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BM + 8, BM + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BM + 8, BM + 24)]) by ut_fp_lia. assert (HWS : sh_fp [(BM + 8, BM + 24)]) by sh_fp_lia.
  assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  assert (EUQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zstep. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia).
  do 4 zstep. zstep. th_if_lit.
  zstep.
  zstep. zstep. th_if_lit.
  zstep.
  zstep. zstep. th_if_lit.
  zstep.
  do 3 zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gr_g2_post, SITE_gr_tail, e_asan_memset, gr_frame, bufmem_cells. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CGrS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_SM : crypto_secure_malloc_env_stmt RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_SCF : crypto_secure_clear_free_env_stmt RT.
Hypothesis MSI : memset_icontract RT e_asan_memset.

(* [comment removed for export] *)
Lemma secre_opt : forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BM D L max n : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 n ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C8 (Z_to_bv 64 1)] ->
  ((D = 0 /\ max = 0) \/ (In (D, max) (rt_live RT Σ) /\ 1 <= max /\ D <> BM)) -> 0 <= L <= max -> L <= n -> max < 2 ^ 40 -> 1 <= n <= 0x8000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 112 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_sec_alloc_realloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) SR_SITES SR_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ -> cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sec_alloc_realloc m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) (SR_W BM) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ sec_off m' /\ rw_cells asegs m' BM [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 max); C8 (Z_to_bv 64 1)]
           /\ wr_at asegs m' q n /\ acc asegs m' q n) c
       /\ rt_live RT Σ' = (q, n) :: live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D L max n outer lb canary
    FDO MST TP A0 A1 INBM BMAL BMC DOPT HL HLN HMAX Hn ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE SEC T c HA Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI.
  destruct DOPT as [(-> & ->) | (IND & HM1 & NDBM)].
  - assert (NZ : forall e, In e (rt_live RT Σ) -> fst e <> 0).
    { intros (p' & n') He. cbn [fst]. pose proof (af_live_range RT AF Σ m p' n' ART0 He). lia. }
    rewrite (live_remove_notin 0 (rt_live RT Σ) NZ) in Hk.
    apply (secre_nd_cps RT AF GOBJ AFP C_SM Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM L 0 n (Z_to_bv 64 1) outer lb canary
             FDO MST TP A0 A1 INBM BMAL BMC Hn ART0 MI0 CALL HSTK CTX UWC
             ltac:(apply (cg_has_sub _ _ _ _ _ CGH); intros e He; unfold SR_SITES, SR_CALLS; cbn [In] in He |- *; clear - He; tauto) Hlen Hcr CLE SEC T c HA).
    intros c' (Σ' & q & H' & REST). apply Hk. exists Σ', q. split; [| exact REST].
    eapply ASTA_conseq; [exact H'|]. cbv beta. intros ms (m' & RS & AFT & PR & CL & SE & WR & ACC). exists m'.
    split; [exact RS|]. split; [exact (rt_after_f_of _ _ _ _ _ _ AFT)|].
    split; [intros x Hx Ho; apply PR; [exact Hx | unfold SR_W in Ho; cbn [outside] in Ho |- *; split; [clear - Ho; lia | exact I]]|].
    split; [exact CL|]. split; [exact SE|]. split; [| exact (conj WR ACC)].
    apply (rw_cells_agree_nw asegs m m' _ _ BMC). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PR; [apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia] | cbn [outside]; unfold G_ALLOW_CUST; split; [clear - Hx BMHI; lia | exact I]].
  - destruct (live_CB RT AF Σ m D max ART0 IND ltac:(clear - HM1; lia)) as (junk & LJ & DC).
    assert (SB : bytes_at asegs m D (firstn (Z.to_nat L) junk)).
    { pose proof (proj2 (proj1 DC)) as DB. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB.
      rewrite <- (firstn_skipn (Z.to_nat L) junk) in DB. exact (proj1 (proj1 (bytes_at_app asegs m D _ _) DB)). }
    assert (LBS : Z.of_nat (length (firstn (Z.to_nat L) junk)) = L) by (rewrite firstn_length, LJ; clear - HL; lia).
    apply (secre_cps RT AF GOBJ AFP C_SM MCP C_SCF Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D L max n (Z_to_bv 64 1)
             (firstn (Z.to_nat L) junk) outer lb canary FDO MST TP A0 A1 INBM BMAL BMC IND NDBM HL HM1 HLN HMAX Hn SB LBS ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE SEC T c HA).
    intros c' (Σ' & q & H' & REST). apply Hk. exists Σ', q. split; [| exact REST].
    eapply ASTA_conseq; [exact H'|]. cbv beta. intros ms (m' & RS & AFT & PR & CL & SE & DW & _ & WR & ACC). exists m'.
    split; [exact RS|]. split; [exact AFT|]. split; [exact PR|]. split; [exact CL|]. split; [exact SE|]. split; [| exact (conj WR ACC)].
    assert (INBM' : In (BM, 32) (live_remove D (rt_live RT Σ))) by (apply live_remove_keep; [exact INBM | cbn [fst]; clear - NDBM; intros E; exact (NDBM (eq_sym E))]).
    assert (AGB : forall x : word, BM <= bv_unsigned x < BM + 32 -> ~ (BM + 8 <= bv_unsigned x < BM + 16) -> m' x = m x).
    { intros x Hx Hno. apply PR; [apply (acl_live _ _ _ BM 32); [exact INBM' | exact Hx] | unfold SR_W; cbn [outside]; unfold G_ALLOW_CUST; clear - Hx Hno BMHI; lia]. }
    pose proof (proj1 (rw_cells_app m BM [C8 (Z_to_bv 64 L)] [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C8 (Z_to_bv 64 1)]) BMC) as (B0 & B1).
    pose proof (rw_cells_skip m _ [C8 (Z_to_bv 64 D)] [C8 (Z_to_bv 64 max); C8 (Z_to_bv 64 1)] B1) as B2. cbn [cells_size csize Nat.add] in B1, B2.
    apply (proj2 (rw_cells_app m' BM [C8 (Z_to_bv 64 L)] [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 max); C8 (Z_to_bv 64 1)])). split.
    + apply (rw_cells_agree_nw asegs m m' _ _ B0). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AGB; clear - Hx; lia.
    + cbn [cells_size csize Nat.add]. apply (proj2 (rw_cells_app m' (BM + 8) [C8 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 max); C8 (Z_to_bv 64 1)])). split; [exact DW|].
      cbn [cells_size csize Nat.add]. replace (BM + 8 + 8) with (BM + Z.of_nat 8 + Z.of_nat 8) by lia.
      apply (rw_cells_agree_nw asegs m m' _ _ B2). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AGB; clear - Hx; lia.
Qed.

Definition GRS_SITES : list (Z * Z) := (SITE_gr_secre, e_BUF_MEM_grow_clean) :: SR_SITES.
Definition GRS_CALLS : list (Z * Z) := (SITE_gr_secre, e_sec_alloc_realloc) :: SR_CALLS.

(* [comment removed for export] *)
Definition grow_sec_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BM D len max len' : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BM -> a1 = Z_to_bv 64 len' ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 1)) -> data_opt (rt_live RT Σ) BM D max ->
  0 <= len <= max -> max < len' -> gr_n len' <= 0x8000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 144 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_BUF_MEM_grow_clean (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) GRS_SITES GRS_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (gr_n len') <= rt_credit RT Σ -> cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BUF_MEM_grow_clean m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 len') m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) (GR_W BM) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ sec_off m' /\ rw_cells asegs m' BM (bufmem_cells len' q (gr_n len') (Z_to_bv 64 1))) c
       /\ rt_live RT Σ' = (q, gr_n len') :: live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (gr_n len') /\ 0 < q /\ q mod 16 = 0 /\ q + gr_n len' < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem grow_sec_cps : grow_sec_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D len max len' outer lb canary
    FDO MST -> -> -> INBM BMAL BMC DOPT HLEN HLT HN4 ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE SEC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 80 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80). set (n := gr_n len') in *. pose proof (gr_n_gt len' ltac:(clear - HLEN HLT; lia)) as HNGT. fold n in HNGT.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI. pose proof (proj2 (af_acc_live RT AF Σ m BM 32 ART0 INBM)) as ACCBM.
  assert (DRNG : 0 <= D /\ D + max < 2 ^ 63 /\ D <> BM /\ (D + max <= BM \/ BM + 32 <= D)).
  { destruct DOPT as [(-> & ->) | (IND & HM1 & NDBM)]; [clear - BM0; lia|].
    pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _).
    pose proof (live_ne_apart RT AF Σ m D max BM 32 ART0 IND INBM ltac:(intros E; injection E; intros _; exact NDBM)). clear - D0 DLO' LOW HLO1 SPH H NDBM. lia. }
  destruct DRNG as (D0 & DMAX & NDBM & APDBM).
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 5). lia. }
  (* [comment removed for export] *)
  pose proof (gr_g0_walk ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BM D len max len' 1 (Z_to_bv 64 1)
                HLO1 HLOS SPH ST UT SHC BMC (flags_byte m BM len D max 1 (or_intror eq_refl) BMC) ACCBM BM0 BMAL BMHI BMLO D0 DMAX HLEN HLT
                ltac:(clear - HN4 HNGT; lia) (or_intror eq_refl) MI0) as W0.
  fold usp in W0. fold usp1 in W0. fold n in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a2x & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. cbn [Z.eqb] in Hc1'.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 80 _ ART0 ltac:(lia) ltac:(lia) Hx); lia. }
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros x Hx; cbv beta in Hx; apply P1; apply acl_stack; exact Hx).
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_BUF_MEM_grow_clean e_sec_alloc_realloc SITE_gr_secre m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (SEC1 : sec_off m1) by (apply (sec_off_agree m m1 SEC); intros a Ha; apply MU1; cbn [outside]; rewrite Ha; unfold SEC_INIT; split; [clear - HLO1 HLOS; lia | exact I]).
  assert (BMC1 : rw_cells asegs m1 BM [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 max); C8 (Z_to_bv 64 1)]).
  { unfold bufmem_cells in BMC. apply (rw_cells_agree_nw asegs m m1 _ _ BMC). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1. apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia]. }
  (* [comment removed for export] *)
  apply (secre_opt Σ PMc (Z_to_bv 64 SITE_gr_secre) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 len') (Z_to_bv 64 BM) (Z_to_bv 64 n) a2x
           (Z_to_bv 64 12297829383904690176) a4 a5 a6 a7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880)) s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo BM D len max n (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl eq_refl eq_refl INBM BMAL BMC1).
  { destruct DOPT as [(-> & ->) | (IND & HM1 & _)]; [left; split; reflexivity | right; split; [exact IND | split; [exact HM1 | exact NDBM]]]. }
  { exact HLEN. } { clear - HLEN HLT HNGT; lia. } { clear - HLEN HLT HNGT HN4; lia. } { clear - HLEN HLT HNGT HN4; lia. }
  { exact ART1. } { exact MI1. } { exact CO1. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_gr_secre) by (unfold SITE_gr_secre; lia). exact CTX1. }
  { exact UWC1. }
  { apply (cg_has_sub _ _ _ _ _ CGH); intros e He; [right | right]; exact He. }
  { exact Hlen. } { exact Hcr. } { exact CLE1. } { exact SEC1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & q & Hc2 & LV1 & FRS1 & SP1 & CR1 & Q0 & Q16 & QU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & CLE2 & SEC2 & BMC2' & WRQ & ACCQ) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_gr_secre) in Hc2' by (unfold SITE_gr_secre; lia).
  assert (INBM1 : In (BM, 32) (rt_live RT Σ1)).
  { rewrite LV1. right. apply live_remove_keep; [exact INBM | cbn [fst]; clear - NDBM; lia]. }
  assert (P2 : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST ->
                 ~ (BM + 8 <= bv_unsigned x < BM + 16) -> m2 x = m x).
  { intros x Hx HnL HnB. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(unfold SR_W; cbn [outside]; clear - HnL HnB; lia)).
    apply P1. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; exact (live_remove_sub _ _ _ He) | auto | lia]. }
  assert (FR2 : rw_cells asegs m2 usp1 (CB 8 j :: gr_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold gr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold SR_W, G_ALLOW_CUST; cbn [outside]; unfold usp1, RT_STACK in *; clear - Hx NUM HSTK BMLO HLO1; lia]. }
  assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len 0 max (Z_to_bv 64 1))) by (unfold bufmem_cells; exact BMC2').
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2). pose proof (proj2 (af_acc_live RT AF Σ1 m2 BM 32 ART2 INBM1)) as ACCBM2.
  (* [comment removed for export] *)
  pose proof (gr_g2s_walk ra (Z_to_bv 64 SITE_gr_secre) sp gp u0 u1 u2 s0 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo BM 0 q n len max len' (Z_to_bv 64 1) j
                HLO1 HLOS SPH ST2 UT2 SHC2 FR2 BMC2 ACCBM2 BM0 BMAL BMHI BMLO Q0 ltac:(unfold USTACK_TOP in QU; clear - QU; lia) ltac:(clear - HNGT HLEN HLT; lia)
                ltac:(clear - HLEN HLT; lia) ltac:(clear - HNGT HN4; lia) ltac:(clear; lia) ltac:(clear - D0 DMAX HLEN; lia) MI2) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & FR3 & ST3 & BMC3) & Hc3'). clear Hc3.
  fold usp in FR3, ST3, Hc3'. fold usp1 in FR3, ST3, Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ BM 32); [exact INBM1 | clear - Hin; lia]. }
  assert (CO3 : call_ok RT Σ1 m3 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP1; exact (conj ST3 (conj LOW COP))).
  assert (INQ : In (q, n) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  (* [comment removed for export] *)
  apply (MSI Σ1 PMc (Z_to_bv 64 SITE_gr_tail) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 len') (Z_to_bv 64 (q + len)) (Z_to_bv 64 0) (Z_to_bv 64 (len' - len))
           b3 b4 b5 b6 b7 (Z_to_bv 64 BM) (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
           s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 (q + len) (len' - len) (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl
           ltac:(unfold USTACK_TOP in QU; clear - Q0 QU HLEN HLT HNGT; lia) ltac:(clear - HLEN HLT HNGT HN4; lia)).
  { exact (live_checked_dst RT AF Σ1 m3 _ q n (q + len) (len' - len) ART3 INQ ltac:(clear - HLEN; lia) ltac:(clear - HNGT; lia) ltac:(clear - HLEN HLT; lia)). }
  { exact ART3. } { exact MI3. } { exact CO3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ZB4) & Hc4'). clear Hc4.
  destruct RS4 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_gr_tail) in Hc4' by (unfold SITE_gr_tail; lia).
  assert (NQ : forall x, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp x -> ~ (q <= x < q + n)).
  { intros x Hx. rewrite <- FRS1 in Hx. exact (fresh_apart RT AF Σ1 m2 q n _ usp x ART2 LV1 ltac:(rewrite SP1; lia) ltac:(clear - HNGT HLEN HLT; lia) Hx). }
  assert (P4 : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST ->
                 ~ (BM + 8 <= bv_unsigned x < BM + 24) -> m4 x = m x).
  { intros x Hx HnL HnB. rewrite (PRES4 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He | auto | unfold usp1; lia]) ltac:(pose proof (NQ _ Hx); clear - H HLEN HLT HNGT; lia)).
    rewrite (MU3 x ltac:(cbn [outside]; clear - HnB; lia)). exact (P2 x Hx HnL ltac:(clear - HnB; lia)). }
  assert (FR4 : rw_cells asegs m4 usp1 (CB 8 j :: gr_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4]. intros x Hx. cbv beta in Hx. unfold gr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    pose proof (af_live_range RT AF Σ1 m2 q n ART2 INQ) as (_ & QLO & _). rewrite SP1 in QLO.
    apply PRES4; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold usp1 in Hx; clear - Hx QLO NUM HLEN HLT HNGT; lia]. }
  assert (BMC4 : rw_cells asegs m4 BM (bufmem_cells len q n (Z_to_bv 64 1))).
  { apply (rw_cells_agree asegs m3 m4 _ _ BMC3); [| exact WM4]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    pose proof (af_live_disj RT AF Σ1 m2 q n BM 32 [] (live_remove D (rt_live RT Σ)) ART2 LV1 ltac:(apply live_remove_keep; [exact INBM | cbn [fst]; clear - NDBM; lia])) as DQB.
    apply PRES4; [apply (acl_live _ _ _ BM 32); [exact INBM1 | clear - Hx; lia] | clear - Hx DQB HLEN HLT HNGT; lia]. }
  destruct (af_client_consts RT AF Σ1 m4 ART4) as (_ & _ & _ & _ & UT4).
  (* [comment removed for export] *)
  pose proof (gr_tail_walk ra sp gp y0 y1 y2 s0 s1 (Z_to_bv 64 (q + len)) h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
                (Z_to_bv 64 (BM + 16)) (Z_to_bv 64 n) (Z_to_bv 64 (BM ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BM + 16) ≫ 3 + 2147450880))
                F4 fc4 m4 lo BM q len n len' (Z_to_bv 64 1) j HLO1 HLOS SPH ST4 UT4 FR4 BMC4 (proj2 (af_acc_live RT AF _ m4 BM 32 ART4 INBM1)) BM0 BMAL BMHI BMLO ltac:(clear - HLEN HLT HNGT HN4; lia) MI4) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc4' c5 Hc5.
  apply Hk. exists Σ1, q.
  split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 (conj Q0 (conj Q16 (conj QU CG1)))))))].
  eapply ASTA_conseq; [exact Hc5|]. intros ms (z0 & z1 & z2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z3 & z4 & z5 & z6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & BMC5).
  fold usp in ST5. exists m5. split; [do 16 eexists; reflexivity|].
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 usp1 ART4 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM5].
    intros x Hx. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ BM 32); [exact INBM1 | clear - Hin; lia]. }
  split; [exact (conj ART5 (conj MI5 ST5))|].
  assert (P5 : forall x : word, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (GR_W BM) (bv_unsigned x) -> m5 x = m x).
  { intros x Hx Ho. unfold GR_W, G_ALLOW_CUST in Ho. cbn [outside] in Ho. rewrite (MU5 x ltac:(cbn [outside]; clear - Ho; lia)). apply P4; [exact Hx | unfold G_ALLOW_CUST; clear - Ho; lia | clear - Ho; lia]. }
  split; [exact P5|].
  assert (CLE3 : cl_env m3 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m2 m3 _ canary CLE2 MU3); cl_fp_lia).
  assert (CLE4 : cl_env m4 (Z_to_bv 8 1) canary).
  { apply (cl_env_pres_ex _ _ _ _ _ m3 m4 _ canary CLE3 PRES4). intros x Hx.
    pose proof (NQ x ltac:(right; left; exact (cl_cell_static _ Hx))). clear - H HLEN HLT HNGT. lia. }
  split; [apply (cl_env_seg _ m4 m5 _ canary CLE4 MU5); cl_fp_lia|].
  split; [| exact BMC5].
  apply (sec_off_agree m m5 SEC). intros a Ha. apply P5; [right; left; rewrite Ha; exact sec_init_static | rewrite Ha; unfold GR_W, SEC_INIT, G_ALLOW_CUST; cbn [outside]; clear - BMHI; lia].
Qed.
End CGrS.
