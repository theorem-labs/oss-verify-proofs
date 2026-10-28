(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_G_CRYPTO_calloc Fz_T_sa Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Definition e_sa_set : Z := 0x20cf18.
Definition SITE_sas_calloc : Z := 0x20cfe4.
Definition sa_delta (val old : word) : Z :=
  if bv_eqb val (Z_to_bv 64 0) then (if bv_eqb old (Z_to_bv 64 0) then 0 else -1) else (if bv_eqb old (Z_to_bv 64 0) then 1 else 0).

Definition SAS_FILE : Z := 0x4baa0.
(* [comment removed for export] *)
Lemma sas_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA : Z),
  0 < SA -> SA mod 8 = 0 -> SA + 32 <= lo ->
  rw_cells asegs m SA (sa_hdr z64 z64 z64 z64 z64) -> acc asegs m SA 32 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 96 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_sas_calloc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp a2 (Z_to_bv 64 16) (Z_to_bv 64 8) (Z_to_bv 64 SAS_FILE) (Z_to_bv 64 176) a4 a5 a6 a7
                    (Z_to_bv 64 SA) z64 (Z_to_bv 64 (SA + 24)) (Z_to_bv 64 SAS_FILE) (Z_to_bv 64 SHB) (Z_to_bv 64 1)
                    (Z_to_bv 64 (Z.shiftr SA 3 + SHB)) (Z_to_bv 64 (Z.shiftr (SA + 24) 3 + SHB)) (Z_to_bv 64 (Z.land SA 7 + 3)) s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_CRYPTO_calloc) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk asegs m' lo (bv_unsigned sp + -96) /\ rw_cells asegs m' SA (sa_hdr z64 z64 z64 z64 z64))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SA) z64 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sa_set) fc None m (seg_rom asegs)).
Proof.
  intros until SA. intros SA0 PAL SALO HC ACC UT SHC ST LO0 LO HTOP MI. unfold e_sa_set, sa_hdr, g_shadow_memory_dynamic_address, SHB, SITE_sas_calloc, SAS_FILE, e_CRYPTO_calloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 14 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 8 zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  do 2 zstep.
  zstep. th_if_lit.                                                                     (* [comment removed for export] *)
  do 6 zstep.
  do 4 zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [eassumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma sas_w1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA P : Z)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  0x10007fff8000 <= SA -> SA mod 8 = 0 -> SA + 32 <= lo -> 0x10007fff8000 <= P -> P mod 8 = 0 -> P + 128 <= lo -> (SA + 32 <= P \/ P + 128 <= SA) -> bv_unsigned val <> 0 ->
  rw_cells asegs m SA (sa_hdr z64 z64 z64 z64 z64) -> acc asegs m SA 32 ->
  rw_cells asegs m P [C8 z64; CB 120 (repeat (Z_to_bv 8 0) 120)] -> acc asegs m P 128 ->
  rw_cells asegs m (bv_unsigned sp + -96) [C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 96 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' a2' a3' : word) (m' : mem),
       ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (SA, SA + 4); (SA + 16, SA + 32); (P, P + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 P))
       /\ rw_cells asegs m' P [C8 val; CB 120 (repeat (Z_to_bv 8 0) 120)])
    (MS (mkR (Z_to_bv 64 SITE_sas_calloc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp val (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 SA) z64 (Z_to_bv 64 (SA + 24)) (Z_to_bv 64 SAS_FILE) (Z_to_bv 64 SHB) (Z_to_bv 64 1)
            (Z_to_bv 64 (Z.shiftr SA 3 + SHB)) (Z_to_bv 64 (Z.shiftr (SA + 24) 3 + SHB)) (Z_to_bv 64 (Z.land SA 7 + 3)) s11v t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_sas_calloc) fc None m (seg_rom asegs)).
Proof.
  intros until s11v. intros SA0 PAL SALO P0 PAL2 PLO DISJ HV HC ACC PC ACCP FR UT SHC ST LO0 LO HTOP MI.
  unfold sa_hdr, g_shadow_memory_dynamic_address, SHB, SITE_sas_calloc, SAS_FILE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 val) as RV. unfold bv_modulus in RV. cbn in RV.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (SA, SA + 4); (SA + 16, SA + 32); (P, P + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-96) EU1.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstep. zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep. fix_lit_store. zstep. fix_lit_store.
  zstep. zstep. th_if_lit.
  zstep. zstep.                                                    (* [comment removed for export] *)
  zstep. fix_lit_store.
  zstep. th_if_lit.
  zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }                           (* [comment removed for export] *)
  do 4 zstep. th_if_lit.
  zstep. zstep. zstep. th_if_lit.                                                       (* [comment removed for export] *)
  do 3 zstep.
  zstep. zstep. zstep. zstep. th_if_lit. zstep.
  zstep. if_cases K6; zify_cond K6. { exfalso. rewrite ?unsigned_lit in K6 by lia. lia. } (* [comment removed for export] *)
  zstep. th_if_lit.                                                              (* [comment removed for export] *)
  zstep. zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. fix_lit_store.                                                  (* [comment removed for export] *)
  zstep. zstep. th_if_lit.
  zstep. fix_lit_store. zstep.                                                          (* [comment removed for export] *)
  do 13 zstep.
  th_release FR (bv_unsigned sp).
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Definition T_sa_set_leaf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA n NODES : Z) (pad top ne oldv : word),
    a0 = Z_to_bv 64 SA -> 0x10007fff8000 <= SA -> SA mod 8 = 0 -> SA + 32 <= lo -> a1 = Z_to_bv 64 n -> 0 <= n < 16 ->
    rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 NODES)) -> acc asegs m SA 32 ->
    0x10007fff8000 <= NODES -> NODES mod 8 = 0 -> NODES + 128 <= lo ->
    rw_cells asegs m (NODES + 8 * n) [C8 oldv] -> acc asegs m NODES 128 -> (SA + 32 <= NODES \/ NODES + 128 <= SA) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a1' a2' a3' : word) (top' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (SA + 8, SA + 24); (NODES + 8 * n, NODES + 8 * n + 8)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ bv_unsigned top' = Z.max (bv_unsigned top) n
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 (bv_unsigned ne + sa_delta a2 oldv)) (Z_to_bv 64 NODES))
                 /\ rw_cells asegs m' (NODES + 8 * n) [C8 a2])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_sa_set) fc None m (seg_rom asegs)).

Theorem T_sa_set_leaf_proof : T_sa_set_leaf_stmt.
Proof.
  unfold T_sa_set_leaf_stmt, sa_hdr, g_shadow_memory_dynamic_address, SHB, e_sa_set. intros until oldv.
  intros -> SAHI SAAL SALO -> HN HC ACC NHI NAL NLO VC ACCN DISJ UT SHC ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 top) as RTOP. unfold bv_modulus in RTOP. cbn in RTOP.
  pose proof (bv_unsigned_in_range 64 a2) as RV. unfold bv_modulus in RV. cbn in RV.
  pose proof (bv_unsigned_in_range 64 oldv) as RO. unfold bv_modulus in RO. cbn in RO.
  pose proof (bv_unsigned_in_range 64 ne) as RNE. unfold bv_modulus in RNE. cbn in RNE.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (SA + 8, SA + 24); (NODES + 8 * n, NODES + 8 * n + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Pn := NODES + 8 * n) in *.
  assert (HPn : NODES <= Pn /\ Pn + 8 <= NODES + 128) by (unfold Pn; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ ?Q _ =>
  assert (TAIL : forall (topw a1x : word) (mc : mem),
    rw_cells asegs mc SA [C4 (Z_to_bv 64 1); C4 pad; C8 topw; C8 ne; C8 (Z_to_bv 64 NODES)] -> rw_cells asegs mc Pn [C8 oldv] ->
    rw_cells asegs mc (bv_unsigned sp + -96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mc lo (bv_unsigned sp + -96) -> mem_inv asegs mc ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (SA + 8, SA + 24); (Pn, Pn + 8)]%Z m mc -> wmono asegs m mc ->
    bv_unsigned topw = Z.max (bv_unsigned top) n ->
    evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp a2 (Z_to_bv 64 (SA + 8)) (Z_to_bv 64 1) a1x top a4 a5 a6 a7
                          (Z_to_bv 64 SA) (Z_to_bv 64 n) (Z_to_bv 64 (SA + 24)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr SA 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x20d05c) fc None mc (seg_rom asegs))) end.
  { intros topw a1x mc HCc VCc FRc STc MIc MUc WMc HTOPW. clear HC VC ST MI MU WM.
    cbv beta delta [mkR].
    do 3 zstep. zstep. th_if_lit.
    do 2 zstep. zstep. th_if_lit.
    do 3 zstep. rewrite (sa_slot n HN). fold Pn.
    zstep. zstep. zstep. zstep. th_if_lit. zstep.
    zstep. unfold sa_delta. destruct (bv_eqb a2 (Z_to_bv 64 0)) eqn:EV; cbv iota.      (* [comment removed for export] *)
    - zstep. destruct (bv_eqb oldv (Z_to_bv 64 0)) eqn:EO; cbv iota.
      + zstep. zstep. th_if_lit. zstep. fix_lit_store. zstep.
        do 13 zstep. th_release FRc (bv_unsigned sp). zstep. finish. exact HTOPW. exact HCc.
      + zstep. zstep. do 3 zstep. zstep. th_if_lit.
        zstep. zstep. zstep. fix_lit_store.
        zstep. zstep. th_if_lit. zstep. fix_lit_store. zstep.
        do 13 zstep. th_release FRc (bv_unsigned sp). zstep. finish. exact HTOPW. exact HCc.
    - zstep. destruct (bv_eqb oldv (Z_to_bv 64 0)) eqn:EO; cbv beta iota delta [negb].
      + zstep. zstep.
        zstep. do 3 zstep. zstep. th_if_lit.
        zstep. zstep. zstep. fix_lit_store.
        zstep. zstep. th_if_lit. zstep. fix_lit_store. zstep.
        do 13 zstep. th_release FRc (bv_unsigned sp). zstep. finish. exact HTOPW. exact HCc.
      + zstep. zstep. th_if_lit. zstep. fix_lit_store. zstep.
        do 13 zstep. th_release FRc (bv_unsigned sp). zstep. finish. exact HTOPW. exact HCc. }
  th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 14 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 8 zstep. zstep. if_cases K16; zify_cond K16. 2:{ exfalso. rewrite ?unsigned_lit in K16 by lia. lia. }
  do 3 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small 1) by lia.
  zstep. zstep. th_if_lit.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases KT; zify_cond KT.                                             (* [comment removed for export] *)
  - eapply TAIL; try eassumption. lia.
  - zstep. zstep. th_if_lit. zstep. fix_lit_store. eapply TAIL; try eassumption. rewrite unsigned_lit by lia. lia.
Qed.

Section CSas.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CALLOC : CRYPTO_calloc_stmt RT.

Definition SAS_SITES : list (Z * Z) := [(SITE_sas_calloc, e_sa_set); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition SAS_CALLS : list (Z * Z) := [(SITE_sas_calloc, e_CRYPTO_calloc); (SITE_sas_calloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].

(* [comment removed for export] *)
Definition sa_set_fresh_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (SA : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 0 -> bv_unsigned a2 <> 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x190 <= bv_unsigned sp ->      (* [comment removed for export] *)
  cg_ctx (rt_cg RT Σ) e_sa_set (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) SAS_SITES SAS_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  In (SA, 32) (rt_live RT Σ) -> SA mod 8 = 0 -> rw_cells asegs m SA (sa_hdr z64 z64 z64 z64 z64) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sa_set m)))
    (fun c => exists (Σ' : rts RT) (P : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (SA, SA + 32)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 P))
           /\ rw_cells asegs m' P [C8 a2; CB 120 (repeat (Z_to_bv 8 0) 120)]) c
       /\ rt_live RT Σ' = (P, 128) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem sa_set_fresh_cps : sa_set_fresh_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary SA
    FDO MST -> -> -> HV ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE INSA SAAL HC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 384 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -96).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m SA 32 ART0 INSA) as (SA0 & SALO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m SA 32 ART0 INSA ltac:(lia)) as SAHI.
  pose proof (proj2 (af_acc_live RT AF Σ m SA 32 ART0 INSA)) as ACC0.
  (* [comment removed for export] *)
  pose proof (sas_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo SA
                SA0 SAAL ltac:(clear - SALO LOW; lia) HC ACC0 UT SHC ST HLOS HLO1 SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & HC1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_sa_set e_CRYPTO_calloc SITE_sas_calloc m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  (* [comment removed for export] *)
  apply (C_CALLOC Σ PMc (Z_to_bv 64 SITE_sas_calloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp a2 (Z_to_bv 64 16) (Z_to_bv 64 8) (Z_to_bv 64 SAS_FILE) (Z_to_bv 64 176) a4 a5 a6 a7
           (Z_to_bv 64 SA) (Z_to_bv 64 0) (Z_to_bv 64 (SA + 24)) (Z_to_bv 64 SAS_FILE) (Z_to_bv 64 SHB) (Z_to_bv 64 1)
           (Z_to_bv 64 (Z.shiftr SA 3 + SHB)) (Z_to_bv 64 (Z.shiftr (SA + 24) 3 + SHB)) (Z_to_bv 64 (Z.land SA 7 + 3)) s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl ltac:(rewrite !unsigned_lit by lia; lia) ltac:(vm_compute; reflexivity) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 6. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_sas_calloc) by (unfold SITE_sas_calloc; lia). exact CTX1. }
  { exact UWC1. }
  { rewrite (unsigned_lit SITE_sas_calloc) by (unfold SITE_sas_calloc; lia). apply (proj2 CGH). cbn [SAS_CALLS In]. tauto. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [SAS_SITES SAS_CALLS In] in Hx |- *; clear - Hx; tauto. }
  { exact Hlen. } { rewrite !unsigned_lit by lia. change (mcost (16 * 8)) with 0. exact Hcr. } { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & P & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PU & CG1).
  rewrite !unsigned_lit in LV1, CR1, PU, Hc2 by lia. change (16 * 8) with 128 in *. change (mcost 128) with 0 in CR1.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & WRB & ACCB & ZB) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_sas_calloc) in Hc2' by (unfold SITE_sas_calloc; lia). change (Z.to_nat 128) with 128%nat in ZB.
  assert (INB : In (P, 128) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INSA1 : In (SA, 32) (rt_live RT Σ1)) by (rewrite LV1; right; exact INSA).
  pose proof (af_live_range RT AF Σ1 m2 P 128 ART2 INB) as (_ & PLO & _). rewrite SP1 in PLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 P 128 ART2 INB ltac:(lia)) as PHI.
  pose proof (af_live_disj RT AF Σ1 m2 P 128 SA 32 [] (rt_live RT Σ) ART2 LV1 INSA) as DISJ.
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. unfold G_ALLOW_CUST. cbn [outside]. unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *. clear - H1 H2 Hx NUM LOW HSTK. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (HC2 : rw_cells asegs m2 SA (sa_hdr (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m1 m2 _ _ HC1); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add sa_hdr] in Hx.
    apply PRES2; [apply (acl_live _ _ _ SA 32); [exact INSA | lia]|]. unfold G_ALLOW_CUST. cbn [outside]. clear - Hx SAHI. lia. }
  assert (PC2 : rw_cells asegs m2 P [C8 (Z_to_bv 64 0); CB 120 (repeat (Z_to_bv 8 0) 120)]) by (split; [split; [cbn; repeat split; reflexivity | exact ZB] | exact WRB]).
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (proj2 (af_acc_live RT AF Σ1 m2 SA 32 ART2 INSA1)) as ACC2.
  (* [comment removed for export] *)
  pose proof (sas_w1 sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 a2 F2 fc2 m2 lo SA P ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                SAHI SAAL ltac:(clear - SALO LOW; lia) PHI ltac:(clear - P16; Z.div_mod_to_equations; lia) ltac:(clear - PLO LOW; lia) ltac:(clear - DISJ; lia) HV
                HC2 ACC2 PC2 ACCB FR2 UT2 SHC2 ST2 HLOS HLO1 SPH MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (e1 & e2 & e3 & m3 & -> & MU3 & WM3 & MI3 & ST3 & HC3 & PC3) & Hc3'). clear Hc3.
  fold usp in ST3.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. repeat split; try exact I.
    - intros Hin; apply Hx. left. unfold usp1, USTACK_TOP in *. lia.
    - intros Hin; apply Hx. apply (acl_live _ _ _ SA 32); [exact INSA1 | clear - Hin; lia].
    - intros Hin; apply Hx. apply (acl_live _ _ _ SA 32); [exact INSA1 | clear - Hin; lia].
    - intros Hin; apply Hx. apply (acl_live _ _ _ P 128); [exact INB | clear - Hin; lia]. }
  assert (CRQ : rt_credit RT Σ1 = rt_credit RT Σ) by (rewrite CR1; lia).
  apply Hk. exists Σ1, P.
  split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CRQ (conj P0 (conj P16 (conj PU CG1)))))))].
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3.
  split; [exists u0, u1, u2, e1, e2, e3, b4, b5, b6, b7, u3, u4, u5, u6, F2, fc2; reflexivity|].
  split; [split; [exact ART3 | split; [exact MI3 | split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) | exact ST3]]]|].
  split.
  { intros x Hx Ho. pose proof (newchunk_apart RT AF Σ Σ1 m2 P 128 usp _ ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Hx) as NB.
    pose proof (aclient_split RT AF Σ m usp (bv_unsigned x) ART0 Hx) as SPL. cbn [outside] in Ho. destruct Ho as (O1 & O2 & _).
    rewrite (MU3 x ltac:(unfold usp1 in *; cbn [outside]; clear - NB O2 SPL NUM; repeat split; try exact I; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(cbn [outside]; exact (conj O1 I))). apply PR1; [exact Hx | exact I]. }
  split; [apply (cl_env_seg _ m2 m3 _ canary CLE2 MU3); cl_fp_lia|].
  exact (conj HC3 PC3).
Qed.
End CSas.
