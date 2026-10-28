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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_free Fz_W4_kit Fz_W1_defs Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition SITE_bne_zalloc : Z := 0x249d98.

(* [comment removed for export] *)
Definition bne_s0_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' : word) (flw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bne_zalloc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp flw (Z_to_bv 64 32) (Z_to_bv 64 0x73520) (Z_to_bv 64 35)
                 a3 a4 a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2'; C8 s1'; C8 s0'; C8 ra0] /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma bne_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' flw a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (bne_s0_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' flw lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' flw a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BUF_MEM_new_ex) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC MI. unfold e_BUF_MEM_new_ex, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  zstep. do 4 zstep. zstep. replace (SP + -32 + 32) with SP by lia. do 3 zstep. zstep. do 4 zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bne_s0_post, SITE_bne_zalloc, e_CRYPTO_zalloc. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition bne_s1_post (ra0 sp gp tp s0' s1' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (B lo : Z) (flw : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 B) a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(B, B + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' B (bufmem_cells 0 0 0 flw).

Lemma bne_s1_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B lo : Z) (flw : word),
  stk asegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  bytes_at asegs m B (repeat (Z_to_bv 8 0) 32) -> wr_at asegs m B 32 -> acc asegs m B 32 -> 0 < B -> B mod 16 = 0 -> 0x10007fff8000 <= B -> B + 32 <= lo ->
  mem_inv asegs m ->
  evt asegs (bne_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B lo flw m)
    (MS (mkR (Z_to_bv 64 SITE_bne_zalloc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp flw (Z_to_bv 64 B) a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bne_zalloc) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros ST HLO HLOS SPH UT SHC FR ZB WRB ACCB B0 BAL BHI BLO MI. unfold SITE_bne_zalloc, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(B, B + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(B, B + 32)]) by ut_fp_lia. assert (HWS : sh_fp [(B, B + 32)]) by sh_fp_lia.
  assert (EUB : bv_unsigned (Z_to_bv 64 B) = B) by (apply unsigned_lit; lia).
  assert (BAL8 : B mod 8 = 0) by (clear - BAL; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  assert (ZC : rw_cells asegs m B [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { split; [split; [cbn; repeat split; reflexivity | exact ZB] | exact WRB]. }
  zstep. if_cases KB; zify_cond KB. { exfalso. lia. }
  zstep. do 3 zstep. zstep. th_if_lit. zstep.
  do 4 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bne_s1_post, bufmem_cells. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

Section CBne.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.

Definition BNE_SITES : list (Z * Z) := [(SITE_bne_zalloc, e_BUF_MEM_new_ex); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition BNE_CALLS : list (Z * Z) := [(SITE_bne_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].

(* [comment removed for export] *)
Definition buf_new_ex_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 288 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_BUF_MEM_new_ex (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) BNE_SITES BNE_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BUF_MEM_new_ex m)))
    (fun c => exists (Σ' : rts RT) (B : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 B) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ rw_cells asegs m' B (bufmem_cells 0 0 0 a0) /\ acc asegs m' B 32) c
       /\ rt_live RT Σ' = (B, 32) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ 0 < B /\ B mod 16 = 0 /\ B + 32 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem buf_new_ex_cps : buf_new_ex_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 288 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -32).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 32) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  pose proof (bne_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST HLO1 HLOS SPH UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_BUF_MEM_new_ex e_CRYPTO_zalloc SITE_bne_zalloc m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  (* [comment removed for export] *)
  apply (C_CZ Σ PMc (Z_to_bv 64 SITE_bne_zalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp a0 (Z_to_bv 64 32) (Z_to_bv 64 0x73520) (Z_to_bv 64 35) a3 a4 a5 a6 a7
           (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 32 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 2. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_bne_zalloc) by (unfold SITE_bne_zalloc; lia). exact CTX1. }
  { exact UWC1. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [BNE_SITES BNE_CALLS In] in Hx |- *; clear - Hx; tauto. }
  { exact Hlen. } { change (mcost 32) with 0. exact Hcr. } { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & B & Hc2 & LV1 & FRS1 & SP1 & CR1 & B0 & B16 & BU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & WRB & ACCB & ZB) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_bne_zalloc) in Hc2' by (unfold SITE_bne_zalloc; lia). change (Z.to_nat 32) with 32%nat in ZB.
  assert (INB : In (B, 32) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 B 32 ART2 INB) as (_ & BLO & _). rewrite SP1 in BLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 B 32 ART2 INB ltac:(lia)) as BHI.
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. unfold G_ALLOW_CUST. cbn [outside]. unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *. clear - H1 H2 Hx NUM LOW HSTK. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (bne_s1_walk ra sp gp u0 u1 u2 s0 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 B lo a0
                ST2 HLO1 HLOS SPH UT2 SHC2 FR2 ZB WRB ACCB B0 B16 BHI ltac:(clear - BLO LOW; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & BC3) & Hc3'). clear Hc3.
  fold usp in ST3.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ B 32); [exact INB | clear - Hin; lia]. }
  assert (CRQ : rt_credit RT Σ1 = rt_credit RT Σ) by (rewrite CR1; change (mcost 32) with 0; lia).
  apply Hk. exists Σ1, B.
  split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CRQ (conj B0 (conj B16 (conj BU CG1)))))))].
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3.
  split; [exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F2, fc2; reflexivity|].
  split; [split; [exact ART3 | split; [exact MI3 | split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) | exact ST3]]]|].
  split.
  { intros x Hx Ho. pose proof (newchunk_apart RT AF Σ Σ1 m2 B 32 usp _ ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Hx) as NB.
    rewrite (MU3 x ltac:(cbn [outside]; clear - NB; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) Ho). apply PR1; [exact Hx | exact I]. }
  split; [apply (cl_env_seg _ m2 m3 _ canary CLE2 MU3); cl_fp_lia|].
  split; [exact BC3|].
  exact (proj2 (af_acc_live RT AF Σ1 m3 B 32 ART3 INB)).
Qed.
End CBne.

Definition SITE_mi_zalloc1 : Z := 0x305230.
Definition SITE_mi_bne : Z := 0x305240.
Definition SITE_mi_zalloc2 : Z := 0x305270.
Definition SITE_mi_memcpy : Z := 0x3052a4.
Definition MEM_FILE_LIT : Z := 0xa0ea0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mi_s0_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' : word) (BI : Z) (flw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_mi_zalloc1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1' (Z_to_bv 64 16) (Z_to_bv 64 MEM_FILE_LIT) (Z_to_bv 64 111)
                 a3 a4 a5 a6 a7 (Z_to_bv 64 BI) flw (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma mi_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' flw a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BI lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (mi_s0_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' BI flw lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 BI) flw a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_init) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC MI. unfold e_mem_init, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 6 zstep. zstep. replace (SP + -48 + 48) with SP by lia. zstep. do 3 zstep. zstep. do 4 zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold mi_s0_post, SITE_mi_zalloc1, e_CRYPTO_zalloc, MEM_FILE_LIT. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma mi_s1_walk : forall sp gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (BI bb : Z) (flw : word),
  0 < bb < 2^64 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_mi_bne) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 bb) flw a1 a2
                                    a3 a4 a5 a6 a7 (Z_to_bv 64 BI) flw (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 e_BUF_MEM_new_ex) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_mi_zalloc1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 bb) a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 BI) flw (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mi_zalloc1) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros HBB MI. unfold SITE_mi_zalloc1 in *.
  zstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  do 3 zstep.
  unfold SITE_mi_bne, e_BUF_MEM_new_ex. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition mi_s2_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (BI bb B : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_mi_zalloc2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 bb) (Z_to_bv 64 32) (Z_to_bv 64 MEM_FILE_LIT) (Z_to_bv 64 119)
                 a3 a4 a5 a6 a7 (Z_to_bv 64 BI) (Z_to_bv 64 (bb ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(bb, bb + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' bb [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 0)].

Lemma mi_s2_walk : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo BI bb B : Z) (flw : word),
  lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m bb [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> acc asegs m bb 16 -> 0 < bb -> bb mod 16 = 0 -> 0x10007fff8000 <= bb -> bb + 16 <= lo ->
  0 < B < 2^64 -> mem_inv asegs m ->
  evt asegs (mi_s2_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BI bb B m)
    (MS (mkR (Z_to_bv 64 SITE_mi_bne) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 bb) (Z_to_bv 64 B) a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 BI) flw (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mi_bne) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros HLO HLOS SPH UT SHC BBC ACCBB BB0 BBAL BBHI BBLO HB MI. unfold SITE_mi_bne, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(bb, bb + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(bb, bb + 8)]) by ut_fp_lia. assert (HWS : sh_fp [(bb, bb + 8)]) by sh_fp_lia.
  assert (BBAL8 : bb mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (EUB : bv_unsigned (Z_to_bv 64 B) = B) by (apply unsigned_lit; lia).
  do 3 zstep. zstep. th_if_lit. zstep.
  zstep. if_cases K; zify_cond K. { exfalso. lia. }
  do 4 zstep. zstep.
  subst SP.
  unfold mi_s2_post, SITE_mi_zalloc2, e_CRYPTO_zalloc, MEM_FILE_LIT. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Definition mi_s3_post (sp gp tp a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (BI bb B R : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_mi_memcpy) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 bb) (Z_to_bv 64 R) (Z_to_bv 64 B) (Z_to_bv 64 32)
                 a3 a4 a5 a6 a7 (Z_to_bv 64 BI) (Z_to_bv 64 (bb ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memcpy) fc None m' (seg_rom asegs)
    /\ munch [(bb + 8, bb + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' bb [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 R)].

Lemma mi_s3_walk : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo BI bb B R : Z),
  lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m bb [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 0)] -> acc asegs m bb 16 -> 0 < bb -> bb mod 16 = 0 -> 0x10007fff8000 <= bb -> bb + 16 <= lo ->
  0 < R < 2^64 -> mem_inv asegs m ->
  evt asegs (mi_s3_post sp gp (Z_to_bv 64 0xba3ef0) a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BI bb B R m)
    (MS (mkR (Z_to_bv 64 SITE_mi_zalloc2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 bb) (Z_to_bv 64 R) a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 BI) (Z_to_bv 64 (bb ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mi_zalloc2) fc None m (seg_rom asegs)).
Proof.
  intros until R. intros HLO HLOS SPH UT SHC BBC ACCBB BB0 BBAL BBHI BBLO HR MI. unfold SITE_mi_zalloc2, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(bb + 8, bb + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(bb + 8, bb + 16)]) by ut_fp_lia. assert (HWS : sh_fp [(bb + 8, bb + 16)]) by sh_fp_lia.
  assert (BBAL8 : bb mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (EUR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  do 4 zstep. zstep. th_if_lit. zstep.
  zstep. zstep. th_if_lit. zstep.
  zstep. if_cases K; zify_cond K. { exfalso. lia. }
  zstep. zstep.
  subst SP.
  unfold mi_s3_post, SITE_mi_memcpy, e_asan_memcpy. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Definition mi_s4_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (BI bb lo : Z) (fl : Z) (rrw padw : word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(BI + 40, BI + 72)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.lor fl 4096) rrw (Z_to_bv 64 (-1)) padw (Z_to_bv 64 bb)).

Lemma mi_s4_walk : forall ra0 sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (s0' s1' s2' s3' s4' : word)
    (F : bvmap 5 word) fc (m : mem) (lo BI nbi bb : Z) (fl : Z) (iw shw rrw numw padw ptrw : word),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw ptrw) -> fl_ok fl ->
  acc asegs m BI nbi -> 72 <= nbi -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + nbi <= lo -> 0 < bb < 2^64 -> mem_inv asegs m ->
  evt asegs (mi_s4_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 F fc BI bb lo fl rrw padw m)
    (MS (mkR (Z_to_bv 64 SITE_mi_memcpy) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 bb) a0 a1 a2
             a3 a4 a5 a6 a7 (Z_to_bv 64 BI) s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_mi_memcpy) fc None m (seg_rom asegs)).
Proof.
  intros until ptrw. intros ST HLO HLOS SPH UT SHC FR BW FLOK ACCBI HN BI0 BIAL BIHI BILO HBB MI. unfold SITE_mi_memcpy, g_shadow_memory_dynamic_address, bio_w1_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BI + 40, BI + 72)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BI + 40, BI + 72)]) by ut_fp_lia. assert (HWS : sh_fp [(BI + 40, BI + 72)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  destruct FLOK as [FLR FLB].
  do 4 zstep. zstep. th_if_lit. zstep. zstep. zstep; lfix.
  do 3 zstep. zstep. th_if_lit. zstep; lfix.
  do 4 zstep. zstep. th_if_lit. zstep. zstep. zstep; lfix.
  do 3 zstep. zstep. th_if_lit. zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. zstep. zstep.
  do 3 zstep. zstep. th_if_lit. zstep.
  zstep. zstep. do 6 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold mi_s4_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Definition bufmem_bytes (len data max : Z) (flw : word) : list byte := cells_bytes (bufmem_cells len data max flw).
Lemma bufmem_bytes_length : forall len data max flw, length (bufmem_bytes len data max flw) = 32%nat.
Proof. intros. reflexivity. Qed.
Lemma bufmem_cells_of_bytes : forall (m : mem) p len data max flw, bytes_at asegs m p (bufmem_bytes len data max flw) -> wr_at asegs m p 32 -> rw_cells asegs m p (bufmem_cells len data max flw).
Proof. intros m p len data max flw B W. split; [split; [cbn; repeat split; reflexivity | exact B] | exact W]. Qed.

Section CMi.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.

Definition MI_SITES : list (Z * Z) :=
  [(SITE_mi_zalloc1, e_mem_init); (SITE_mi_bne, e_mem_init); (SITE_mi_zalloc2, e_mem_init); (SITE_bne_zalloc, e_BUF_MEM_new_ex); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition MI_CALLS : list (Z * Z) :=
  [(SITE_mi_zalloc1, e_CRYPTO_zalloc); (SITE_mi_bne, e_BUF_MEM_new_ex); (SITE_mi_zalloc2, e_CRYPTO_zalloc); (SITE_bne_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].
Definition MI_W (BI : Z) : list (Z * Z) := [(BI + 40, BI + 72); (G_ALLOW_CUST, G_ALLOW_CUST + 1)].

(* [comment removed for export] *)
Definition mem_init_at_stmt (ENTRY : Z) (FLAGS : word -> word) (TAILP : rts RT -> word -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (BI nbi fl : Z) (iw shw rrw numw padw ptrw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> TAILP Σ ra ->
  In (BI, nbi) (rt_live RT Σ) -> 72 <= nbi <= 64512 -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw ptrw) -> fl_ok fl ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 336 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) ENTRY (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) MI_SITES MI_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) + 3 <= LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ENTRY m)))
    (fun c => exists (Σ' : rts RT) (bb B R : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (MI_W BI) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.lor fl 4096) rrw (Z_to_bv 64 (-1)) padw (Z_to_bv 64 bb))
           /\ rw_cells asegs m' bb [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 R)]
           /\ rw_cells asegs m' B (bufmem_cells 0 0 0 (FLAGS a1)) /\ rw_cells asegs m' R (readp_cells 0 0 0 (Z_to_bv 64 0) (FLAGS a1))) c
       /\ rt_live RT Σ' = (R, 32) :: (B, 32) :: (bb, 16) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ 0 < bb /\ bb mod 16 = 0 /\ 0 < B /\ B mod 16 = 0 /\ 0 < R /\ R mod 16 = 0 /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem mem_init_cps : mem_init_at_stmt e_mem_init (fun w => w) (fun _ _ => True).
Proof.
  pose proof (buf_new_ex_cps RT AF GOBJ AFP C_CZ) as C_BNE.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary BI nbi fl iw shw rrw numw padw ptrw
    FDO MST -> -> _ INBI HNBI BIAL BW FLOK ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 336 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -48).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 48) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI nbi ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + nbi <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI nbi ART0 INBI ltac:(lia)) as BIHI.
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 3). lia. }
  (* [comment removed for export] *)
  pose proof (mi_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m BI lo
                ST HLO1 HLOS SPH UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 48 _ ART0 ltac:(lia) ltac:(lia) Hx); lia. }
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros x Hx; cbv beta in Hx; apply P1; apply acl_stack; exact Hx).
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_init e_CRYPTO_zalloc SITE_mi_zalloc1 m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (C_CZ Σ PMc (Z_to_bv 64 SITE_mi_zalloc1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 16) (Z_to_bv 64 MEM_FILE_LIT) (Z_to_bv 64 111) a3 a4 a5 a6 a7
           (Z_to_bv 64 BI) a1 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 16 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1 CO1).
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_mi_zalloc1) by (unfold SITE_mi_zalloc1; lia). exact CTX1. }
  { exact UWC1. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [MI_SITES MI_CALLS In] in Hx |- *; clear - Hx; tauto. }
  { clear - Hlen; lia. } { change (mcost 16) with 0. exact Hcr. } { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & bb & Hc2 & LV1 & FRS1 & SP1 & CR1 & BB0 & BB16 & BBU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & WRBB & ACCBB & ZBB) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_mi_zalloc1) in Hc2' by (unfold SITE_mi_zalloc1; lia). change (Z.to_nat 16) with 16%nat in ZBB.
  assert (INBB : In (bb, 16) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INBI1 : In (BI, nbi) (rt_live RT Σ1)) by (rewrite LV1; right; exact INBI).
  pose proof (af_live_range RT AF Σ1 m2 bb 16 ART2 INBB) as (_ & BBLO' & _). rewrite SP1 in BBLO'. assert (BBLO : bb + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 bb 16 ART2 INBB ltac:(lia)) as BBHI.
  assert (NBB : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (bb <= x < bb + 16)).
  { intros x Hx. exact (newchunk_apart RT AF Σ Σ1 m2 bb 16 usp x ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Hx). }
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m2 x = m x).
  { intros x Hx HnL. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(cbn [outside]; split; [clear - HnL; lia | exact I])). exact (P1 x Hx). }
  assert (BBC2 : rw_cells asegs m2 bb [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (split; [split; [cbn; repeat split; reflexivity | exact ZBB] | exact WRBB]).
  (* [comment removed for export] *)
  pose proof (mi_s1_walk sp gp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 BI bb a1 ltac:(unfold USTACK_TOP in BBU; clear - BB0 BBU; lia) MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  assert (AG12 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. unfold G_ALLOW_CUST. cbn [outside]. unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *. clear - H1 H2 Hx NUM LOW HSTK. lia. }
  cl_keep FR1 AG12 WM2 FR2.
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2).
  { intros x Hx. cbv beta in Hx. apply P2; [apply acl_stack; exact Hx | unfold G_ALLOW_CUST, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - Hx NUM LOW HSTK; lia]. }
  assert (FRR2 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m2 usp1 [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR2). }
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_init e_BUF_MEM_new_ex SITE_mi_bne m m2 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; left; reflexivity)) UWC AG02 FRR2 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX2 & UWC2).
  rewrite <- CG1 in CTX2.
  assert (CO2 : call_ok RT Σ1 m2 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP1; exact (conj ST2 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (C_BNE Σ1 PMc (Z_to_bv 64 SITE_mi_bne) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 bb) a1 b1 b2 b3 b4 b5 b6 b7
           (Z_to_bv 64 BI) a1 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART2 MI2 CO2).
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_mi_bne) by (unfold SITE_mi_bne; lia). exact CTX2. }
  { exact UWC2. }
  { rewrite CG1. split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [BNE_SITES BNE_CALLS MI_SITES MI_CALLS In] in Hx |- *; clear - Hx; tauto. }
  { rewrite LV1. cbn [length]. clear - Hlen; lia. } { rewrite CR1. change (mcost 16) with 0. clear - Hcr; lia. } { exact CLE2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & B & Hc4 & LV2 & FRS2 & SP2 & CR2 & B0 & B16 & BU & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & CLE3 & BC3 & ACCB3) & Hc4'). clear Hc4.
  destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite (ret_pc_even SITE_mi_bne) in Hc4' by (unfold SITE_mi_bne; lia).
  assert (INB2 : In (B, 32) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INBB2 : In (bb, 16) (rt_live RT Σ2)) by (rewrite LV2; right; exact INBB).
  assert (INBI2 : In (BI, nbi) (rt_live RT Σ2)) by (rewrite LV2; right; exact INBI1).
  pose proof (af_live_range RT AF Σ2 m3 B 32 ART3 INB2) as (_ & BLO' & _). rewrite SP2, SP1 in BLO'. assert (BLO : B + 32 <= lo) by (clear - BLO' LOW; lia). clear BLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m3 B 32 ART3 INB2 ltac:(lia)) as BHI.
  assert (NB : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (B <= x < B + 32)).
  { intros x Hx. apply (newchunk_apart RT AF Σ1 Σ2 m3 B 32 usp x ART3 LV2 FRS2 SP2 ltac:(rewrite SP1; lia) ltac:(lia)).
    rewrite LV1, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He | auto | lia]. }
  assert (P3 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m3 x = m x).
  { intros x Hx HnL. rewrite (PRES3 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He | auto | unfold usp1; lia])
      ltac:(cbn [outside]; split; [clear - HnL; lia | exact I])). exact (P2 x Hx HnL). }
  assert (BBC3 : rw_cells asegs m3 bb [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m2 m3 _ _ BBC2); [| exact WM3]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES3; [apply (acl_live _ _ _ bb 16); [exact INBB | lia] | unfold G_ALLOW_CUST; cbn [outside]; clear - Hx BBHI; lia]. }
  destruct (af_client_consts RT AF Σ2 m3 ART3) as (_ & SHC3 & _ & _ & UT3).
  pose proof (proj2 (af_acc_live RT AF Σ2 m3 bb 16 ART3 INBB2)) as ACCBB3.
  (* [comment removed for export] *)
  pose proof (mi_s2_walk sp gp v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m3 lo BI bb B a1
                HLO1 HLOS SPH UT3 SHC3 BBC3 ACCBB3 BB0 BB16 BBHI BBLO ltac:(unfold USTACK_TOP in BU; clear - B0 BU; lia) MI3) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m4 & -> & MU4 & WM4 & MI4 & BBC4) & Hc5'). clear Hc5.
  fold usp in Hc5'. fold usp1 in Hc5'.
  assert (ART4 : ART RT Σ2 m4).
  { apply (af_frame RT AF Σ2 m3 m4 usp1 ART3 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM4].
    intros x Hx. apply MU4. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ bb 16); [exact INBB2 | clear - Hin; lia]. }
  assert (P4 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m4 x = m x).
  { intros x Hx HnL. rewrite (MU4 x ltac:(cbn [outside]; pose proof (NBB _ Hx); lia)). exact (P3 x Hx HnL). }
  assert (ST4 : stk asegs m4 lo usp1) by (apply (stk_agree_nw asegs m3 m4 _ _ ST3); intros x Hx; cbv beta in Hx; apply MU4; cbn [outside]; clear - Hx BBLO; lia).
  assert (FR4 : rw_cells asegs m4 usp1 [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m2 m4 _ _ FR2); [| exact (wmono_trans asegs _ _ _ WM3 WM4)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (MU4 x ltac:(cbn [outside]; unfold usp1, RT_STACK in *; clear - Hx BBLO HSTK; lia)). apply PRES3; [left; unfold usp1 in *; clear - Hx NUM; lia | unfold G_ALLOW_CUST; cbn [outside]; unfold usp1, RT_STACK in *; clear - Hx NUM HSTK; lia]. }
  assert (AG04 : agree_on (fun x => usp <= x < USTACK_TOP) m m4).
  { intros x Hx. cbv beta in Hx. apply P4; [apply acl_stack; exact Hx | unfold G_ALLOW_CUST, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - Hx NUM LOW HSTK; lia]. }
  assert (FRR4 : rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m4 usp1 [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR4). }
  destruct (cl_chain_call (rt_cg RT Σ) e_mem_init e_CRYPTO_zalloc SITE_mi_zalloc2 m m4 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(do 2 right; left; reflexivity)) (proj2 CGH _ ltac:(do 2 right; left; reflexivity)) UWC AG04 FRR4 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX4 & UWC4).
  rewrite <- CG1, <- CG2 in CTX4.
  assert (CLE4 : cl_env m4 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m3 m4 _ canary CLE3 MU4); cl_fp_lia).
  assert (CO4 : call_ok RT Σ2 m4 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP2, SP1; exact (conj ST4 (conj LOW COP))).
  (* [comment removed for export] *)
  apply (C_CZ Σ2 PMc (Z_to_bv 64 SITE_mi_zalloc2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 bb) (Z_to_bv 64 32) (Z_to_bv 64 MEM_FILE_LIT) (Z_to_bv 64 119) d3 d4 d5 d6 d7
           (Z_to_bv 64 BI) (Z_to_bv 64 (bb ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m4 32 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           FDO MST eq_refl eq_refl ltac:(lia) ART4 MI4 CO4).
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_mi_zalloc2) by (unfold SITE_mi_zalloc2; lia). exact CTX4. }
  { exact UWC4. }
  { rewrite CG2, CG1. split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [MI_SITES MI_CALLS In] in Hx |- *; clear - Hx; tauto. }
  { rewrite LV2, LV1. cbn [length]. clear - Hlen; lia. } { rewrite CR2, CR1. change (mcost 32) with 0. change (mcost 16) with 0. clear - Hcr; lia. } { exact CLE4. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & R & Hc6 & LV3 & FRS3 & SP3 & CR3 & R0 & R16 & RU & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & CLE5 & WRR & ACCR & ZR) & Hc6'). clear Hc6.
  destruct RS5 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F5 & fc5 & ->).
  rewrite EU1 in ST5, PRES5. rewrite (ret_pc_even SITE_mi_zalloc2) in Hc6' by (unfold SITE_mi_zalloc2; lia). change (Z.to_nat 32) with 32%nat in ZR.
  assert (INR3 : In (R, 32) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
  assert (INB3 : In (B, 32) (rt_live RT Σ3)) by (rewrite LV3; right; exact INB2).
  assert (INBB3 : In (bb, 16) (rt_live RT Σ3)) by (rewrite LV3; right; exact INBB2).
  assert (INBI3 : In (BI, nbi) (rt_live RT Σ3)) by (rewrite LV3; right; exact INBI2).
  pose proof (af_live_range RT AF Σ3 m5 R 32 ART5 INR3) as (_ & RLO' & _). rewrite SP3, SP2, SP1 in RLO'. assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m5 R 32 ART5 INR3 ltac:(lia)) as RHI.
  assert (NR : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (R <= x < R + 32)).
  { intros x Hx. apply (newchunk_apart RT AF Σ2 Σ3 m5 R 32 usp x ART5 LV3 FRS3 SP3 ltac:(rewrite SP2, SP1; lia) ltac:(lia)).
    rewrite LV2, LV1, FRS2, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; right; exact He | auto | lia]. }
  assert (P5 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m5 x = m x).
  { intros x Hx HnL. rewrite (PRES5 x ltac:(rewrite LV2, LV1, FRS2, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; right; exact He | auto | unfold usp1; lia])
      ltac:(cbn [outside]; split; [clear - HnL; lia | exact I])). exact (P4 x Hx HnL). }
  assert (BBC5 : rw_cells asegs m5 bb [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m4 m5 _ _ BBC4); [| exact WM5]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES5; [apply (acl_live _ _ _ bb 16); [exact INBB2 | lia] | unfold G_ALLOW_CUST; cbn [outside]; clear - Hx BBHI; lia]. }
  destruct (af_client_consts RT AF Σ3 m5 ART5) as (_ & SHC5 & _ & _ & UT5).
  pose proof (proj2 (af_acc_live RT AF Σ3 m5 bb 16 ART5 INBB3)) as ACCBB5.
  (* [comment removed for export] *)
  pose proof (mi_s3_walk sp gp w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F5 fc5 m5 lo BI bb B R
                HLO1 HLOS SPH UT5 SHC5 BBC5 ACCBB5 BB0 BB16 BBHI BBLO ltac:(unfold USTACK_TOP in RU; clear - R0 RU; lia) MI5) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (x0 & x1 & x2 & m6 & -> & MU6 & WM6 & MI6 & BBC6) & Hc7'). clear Hc7.
  fold usp in Hc7'. fold usp1 in Hc7'.
  assert (ART6 : ART RT Σ3 m6).
  { apply (af_frame RT AF Σ3 m5 m6 usp1 ART5 ltac:(rewrite SP3, SP2, SP1; unfold usp1; lia)); [| exact WM6].
    intros x Hx. apply MU6. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ bb 16); [exact INBB3 | clear - Hin; lia]. }
  assert (P6 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m6 x = m x).
  { intros x Hx HnL. rewrite (MU6 x ltac:(cbn [outside]; pose proof (NBB _ Hx); lia)). exact (P5 x Hx HnL). }
  assert (ST6 : stk asegs m6 lo usp1) by (apply (stk_agree_nw asegs m5 m6 _ _ ST5); intros x Hx; cbv beta in Hx; apply MU6; cbn [outside]; clear - Hx BBLO; lia).
  assert (CO6 : call_ok RT Σ3 m6 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1, SP3, SP2, SP1; exact (conj ST6 (conj LOW COP))).
  (* [comment removed for export] *)
  assert (SB6 : bytes_at asegs m6 B (bufmem_bytes 0 0 0 a1)).
  { assert (BC6 : rw_cells asegs m6 B (bufmem_cells 0 0 0 a1)).
    { apply (rw_cells_agree asegs m3 m6 _ _ BC3); [| exact (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 WM6))]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
      pose proof (af_live_disj RT AF Σ2 m3 B 32 bb 16 [] (rt_live RT Σ1) ART3 LV2 INBB) as DB.
      rewrite (MU6 x ltac:(cbn [outside]; clear - Hx DB HNBI; lia)). rewrite (PRES5 x ltac:(apply (acl_live _ _ _ B 32); [exact INB2 | clear - Hx; lia]) ltac:(unfold G_ALLOW_CUST; cbn [outside]; clear - Hx BHI; lia)).
      apply MU4. cbn [outside]. clear - Hx DB HNBI; lia. }
    exact (proj2 (proj1 BC6)). }
  (* [comment removed for export] *)
  apply (MCP Σ3 PMc (Z_to_bv 64 SITE_mi_memcpy) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 sp (Z_to_bv 64 bb) (Z_to_bv 64 R) (Z_to_bv 64 B) (Z_to_bv 64 32) g3 g4 g5 g6 g7
           (Z_to_bv 64 BI) (Z_to_bv 64 (bb ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F5 fc5 m6 R B (bufmem_bytes 0 0 0 a1) lo
           FDO MST eq_refl eq_refl eq_refl ltac:(unfold USTACK_TOP in RU; clear - R0 RU; lia) ltac:(unfold USTACK_TOP in BU; clear - B0 BU; lia) ltac:(rewrite bufmem_bytes_length; lia) SB6).
  { rewrite bufmem_bytes_length. exact (live_checked_src RT AF Σ3 m6 _ lo B 32 B 32 ART6 INB3 ltac:(lia) ltac:(lia) ltac:(rewrite SP3, SP2, SP1; exact LOW)). }
  { rewrite bufmem_bytes_length. exact (live_checked_dst RT AF Σ3 m6 _ R 32 R 32 ART6 INR3 ltac:(lia) ltac:(lia) ltac:(lia)). }
  { rewrite bufmem_bytes_length. pose proof (af_live_disj RT AF Σ3 m5 R 32 B 32 [] (rt_live RT Σ2) ART5 LV3 INB2) as DRB. clear - DRB. lia. }
  { exact ART6. } { exact MI6. } { exact CO6. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & CPR7) & Hc8'). clear Hc8.
  destruct RS7 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F7 & fc7 & ->).
  rewrite EU1 in ST7, PRES7. rewrite bufmem_bytes_length in PRES7. rewrite (ret_pc_even SITE_mi_memcpy) in Hc8' by (unfold SITE_mi_memcpy; lia).
  assert (P7 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x <> G_ALLOW_CUST -> m7 x = m x).
  { intros x Hx HnL. rewrite (PRES7 x ltac:(rewrite LV3, LV2, LV1, FRS3, FRS2, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; right; right; exact He | auto | unfold usp1; lia])
      ltac:(change (Z.of_nat 32) with 32; exact (NR _ Hx))). exact (P6 x Hx HnL). }
  assert (AG27 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m2 m7).
  { intros a' n H1 H2 x Hx. cbv beta in Hx.
    assert (HAx : forall live frames, aclient live frames usp1 (bv_unsigned x)) by (intros; left; clear - H1 H2 Hx; lia).
    rewrite (PRES7 x (HAx _ _) ltac:(change (Z.of_nat 32) with 32; unfold usp1, RT_STACK in *; clear - H1 Hx RLO HSTK; lia)).
    rewrite (MU6 x ltac:(cbn [outside]; unfold usp1, RT_STACK in *; clear - H1 Hx BBLO HSTK; lia)).
    rewrite (PRES5 x (HAx _ _) ltac:(unfold G_ALLOW_CUST; cbn [outside]; unfold usp1, RT_STACK in *; clear - H1 Hx NUM HSTK; lia)).
    rewrite (MU4 x ltac:(cbn [outside]; unfold usp1, RT_STACK in *; clear - H1 Hx BBLO HSTK; lia)).
    apply PRES3; [exact (HAx _ _) | unfold G_ALLOW_CUST; cbn [outside]; unfold usp1, RT_STACK in *; clear - H1 Hx NUM HSTK; lia]. }
  pose proof (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 WM7)))) as WM27.
  cl_keep FR2 AG27 WM27 FR7.
  assert (BW7 : rw_cells asegs m7 (BI + 40) (bio_w1_cells iw shw fl rrw numw padw ptrw)).
  { apply (rw_cells_agree asegs m m7 _ _ BW); [| exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM27))]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P7; [apply (acl_live _ _ _ BI nbi); [exact INBI | clear - Hx HNBI; lia] | unfold G_ALLOW_CUST; clear - Hx BIHI; lia]. }
  destruct (af_client_consts RT AF Σ3 m7 ART7) as (_ & SHC7 & _ & _ & UT7).
  pose proof (proj2 (af_acc_live RT AF Σ3 m7 BI nbi ART7 INBI3)) as ACCBI7.
  (* [comment removed for export] *)
  pose proof (mi_s4_walk ra sp gp y0 y1 y2 (Z_to_bv 64 R) h1 h2 h3 h4 h5 h6 h7 (Z_to_bv 64 (bb ≫ 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 s0 s1 s2 s3 s4 F7 fc7 m7 lo BI nbi bb fl
                iw shw rrw numw padw ptrw ST7 HLO1 HLOS SPH UT7 SHC7 FR7 BW7 FLOK ACCBI7 ltac:(clear - HNBI; lia) BI0 BIAL BIHI BILO ltac:(unfold USTACK_TOP in BBU; clear - BB0 BBU; lia) MI7) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ3 _ _ c9 Hc9) as (ms9 & (z0 & z1 & z2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & z3 & z4 & z5 & z6 & m8 & -> & MU8 & WM8 & MI8 & ST8 & BW8) & Hc9'). clear Hc9.
  fold usp in ST8.
  assert (ART8 : ART RT Σ3 m8).
  { apply (af_frame RT AF Σ3 m7 m8 usp1 ART7 ltac:(rewrite SP3, SP2, SP1; unfold usp1; lia)); [| exact WM8].
    intros x Hx. apply MU8. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ BI nbi); [exact INBI3 | clear - Hin HNBI; lia]. }
  assert (CGQ : rt_cg RT Σ3 = rt_cg RT Σ) by (rewrite CG3, CG2; exact CG1).
  assert (CRQ : rt_credit RT Σ3 = rt_credit RT Σ) by (rewrite CR3, CR2, CR1; change (mcost 32) with 0; change (mcost 16) with 0; lia).
  apply Hk. exists Σ3, bb, B, R.
  split; [| split; [rewrite LV3, LV2, LV1; reflexivity | split; [rewrite FRS3, FRS2; exact FRS1 | split; [rewrite SP3, SP2; exact SP1 | split;
           [exact CRQ | exact (conj BB0 (conj BB16 (conj B0 (conj B16 (conj R0 (conj R16 CGQ))))))]]]]].
  eapply ASTA_conseq; [exact Hc9'|]. intros ms <-. exists m8.
  split; [exists z0, z1, z2, k1, k2, k3, k4, k5, k6, k7, z3, z4, z5, z6, F7, fc7; reflexivity|].
  split; [exact (conj ART8 (conj MI8 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM27 WM8))) ST8)))|].
  split.
  { intros x Hx Ho. unfold MI_W, G_ALLOW_CUST in Ho. cbn [outside] in Ho. rewrite (MU8 x ltac:(cbn [outside]; clear - Ho; lia)). apply P7; [exact Hx | unfold G_ALLOW_CUST; clear - Ho; lia]. }
  assert (CLE6 : cl_env m6 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m5 m6 _ canary CLE5 MU6); cl_fp_lia).
  assert (CLE7 : cl_env m7 (Z_to_bv 8 1) canary).
  { apply (cl_env_pres_ex _ _ _ _ _ m6 m7 _ canary CLE6 PRES7). intros x Hx. change (Z.of_nat 32) with 32. apply NR. right; left; exact (cl_cell_static _ Hx). }
  split; [apply (cl_env_seg _ m7 m8 _ canary CLE7 MU8); cl_fp_lia|].
  split; [exact BW8|].
  pose proof (af_live_disj RT AF Σ1 m2 bb 16 BI nbi [] (rt_live RT Σ) ART2 LV1 INBI) as DBB.
  pose proof (af_live_disj RT AF Σ2 m3 B 32 BI nbi [] ((bb, 16) :: rt_live RT Σ) ART3 ltac:(rewrite LV2, LV1; reflexivity) ltac:(cbn [app]; right; exact INBI)) as DB.
  pose proof (af_live_disj RT AF Σ2 m3 B 32 bb 16 [] (rt_live RT Σ1) ART3 LV2 INBB) as DBBB.
  pose proof (af_live_disj RT AF Σ3 m5 R 32 BI nbi [] ((B, 32) :: (bb, 16) :: rt_live RT Σ) ART5 ltac:(rewrite LV3, LV2, LV1; reflexivity) ltac:(cbn [app]; right; right; exact INBI)) as DR.
  pose proof (af_live_disj RT AF Σ3 m5 R 32 B 32 [] (rt_live RT Σ2) ART5 LV3 INB2) as DRB.
  pose proof (af_live_disj RT AF Σ3 m5 R 32 bb 16 [] ((B, 32) :: rt_live RT Σ1) ART5 ltac:(rewrite LV3, LV2; reflexivity) ltac:(cbn [app]; right; exact INBB)) as DRBB.
  split.
  { apply (rw_cells_agree asegs m6 m8 _ _ BBC6); [| exact (wmono_trans asegs _ _ _ WM7 WM8)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (MU8 x ltac:(cbn [outside]; clear - Hx DBB HNBI; lia)). apply PRES7; [apply (acl_live _ _ _ bb 16); [exact INBB3 | clear - Hx; lia] | change (Z.of_nat 32) with 32; clear - Hx DRBB; lia]. }
  split.
  { apply (rw_cells_agree asegs m3 m8 _ _ BC3); [| exact (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 WM8))))].
    intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (MU8 x ltac:(cbn [outside]; clear - Hx DB HNBI; lia)). rewrite (PRES7 x ltac:(apply (acl_live _ _ _ B 32); [exact INB3 | clear - Hx; lia]) ltac:(change (Z.of_nat 32) with 32; clear - Hx DRB; lia)).
    rewrite (MU6 x ltac:(cbn [outside]; clear - Hx DBBB; lia)). rewrite (PRES5 x ltac:(apply (acl_live _ _ _ B 32); [exact INB2 | clear - Hx; lia]) ltac:(unfold G_ALLOW_CUST; cbn [outside]; clear - Hx BHI; lia)).
    apply MU4. cbn [outside]. clear - Hx DBBB; lia. }
  apply bufmem_cells_of_bytes.
  - apply (bytes_at_agree asegs m7 m8 _ _ CPR7). intros x Hx. cbv beta in Hx. rewrite bufmem_bytes_length in Hx. apply MU8. cbn [outside]. clear - Hx DR HNBI; lia.
  - exact (wr_at_wm m7 m8 _ _ (wr_at_wm m6 m7 _ _ (wr_at_wm m5 m6 _ _ WRR WM6) WM7) WM8).
Qed.

(* [comment removed for export] *)
Definition mn_post (ENTRY FLAG : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists m', ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 FLAG) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_mem_init) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).
Lemma mn_walk0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (mn_post e_mem_new 0 ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_new m).
Proof.
  unfold entry_st, e_mem_new, e_secmem_new. intros until lo; intros ST HLO SPH MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP; rewrite <- (Z_to_bv_bv_unsigned sp); rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 zstep. do 2 zstep. zstep. th_release FR SP. zstep.
  subst SP; rewrite ?Z_to_bv_bv_unsigned.
  unfold mn_post, e_mem_init; apply evt_done; eexists; split; [reflexivity|].
  split; [assumption|]; split; [assumption|]; split; assumption.
Qed.
Lemma mn_walk1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (mn_post e_secmem_new 1 ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_secmem_new m).
Proof.
  unfold entry_st, e_mem_new, e_secmem_new. intros until lo; intros ST HLO SPH MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP; rewrite <- (Z_to_bv_bv_unsigned sp); rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 zstep. do 2 zstep. zstep. th_release FR SP. zstep.
  subst SP; rewrite ?Z_to_bv_bv_unsigned.
  unfold mn_post, e_mem_init; apply evt_done; eexists; split; [reflexivity|].
  split; [assumption|]; split; [assumption|]; split; assumption.
Qed.

Lemma mem_new_tail : forall ENTRY FLAG,
  (forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
     stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
     evt asegs (mn_post ENTRY FLAG ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
       (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ENTRY m)) ->
  mem_init_at_stmt ENTRY (fun _ => Z_to_bv 64 FLAG) (fun Σ ra => In (bv_unsigned ra, e_mem_init) (cg_call (rt_cg RT Σ))).
Proof.
  intros ENTRY FLAG WALK Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary BI nbi fl iw shw rrw numw padw ptrw
    FDO MST TP A0 TAIL INBI HNBI BIAL BW FLOK ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE T c HA Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_live_range RT AF Σ m BI nbi ART0 INBI) as (_ & BILO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m BI nbi ART0 INBI ltac:(lia)) as BIHI.
  pose proof (WALK ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST ltac:(unfold RT_STACK in HSTK; clear - HSTK; lia)
                ltac:(unfold USTACK_TOP in SPT; clear - SPT; lia) MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1.
  pose proof (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 16 [] ART0 ltac:(unfold RT_STACK in *; lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m (bv_unsigned sp) 16 _ ART0 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Hx); lia. }
  apply (mem_init_cps Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 FLAG) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo outer lb canary BI nbi fl iw shw rrw numw padw ptrw
           FDO MST TP A0 I INBI HNBI BIAL).
  { apply (rw_cells_agree asegs m m1 _ _ BW); [| exact WM1]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1. apply (acl_live _ _ _ BI nbi); [exact INBI | clear - Hx HNBI; lia]. }
  { exact FLOK. } { exact ART1. } { exact MI1. } { exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))). } { exact HSTK. }
  { exact (conj TAIL (proj2 CTX)). }
  { exact (uw_chain_agree outer m m1 sp s0 UWC ltac:(intros x Hx; cbv beta in Hx; apply P1; apply acl_stack; exact Hx)). }
  { exact CGH. } { exact Hlen. } { exact Hcr. }
  { exact (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)). }
  { exact Hc1'. }
  intros c2 (Σ' & bb & B & R & Hc2 & REST). apply Hk. exists Σ', bb, B, R. split; [| exact REST].
  eapply ASTA_conseq; [exact Hc2|]. intros ms (m' & RS & (ART' & MI' & WM' & ST') & PRES & REST'). exists m'.
  split; [exact RS|]. split; [exact (conj ART' (conj MI' (conj (wmono_trans asegs _ _ _ WM1 WM') ST')))|]. split; [| exact REST'].
  intros x Hx Ho. rewrite (PRES x Hx Ho). exact (P1 x Hx).
Qed.

Theorem mem_new_cps : mem_init_at_stmt e_mem_new (fun _ => Z_to_bv 64 0) (fun Σ ra => In (bv_unsigned ra, e_mem_init) (cg_call (rt_cg RT Σ))).
Proof. exact (mem_new_tail e_mem_new 0 mn_walk0). Qed.
Theorem secmem_new_cps : mem_init_at_stmt e_secmem_new (fun _ => Z_to_bv 64 1) (fun Σ ra => In (bv_unsigned ra, e_mem_init) (cg_call (rt_cg RT Σ))).
Proof. exact (mem_new_tail e_secmem_new 1 mn_walk1). Qed.
End CMi.
