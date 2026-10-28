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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_W1_defs Fz_W1_new Fz_W1_sync Fz_W1_misc Fz_W1_ctrl Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_BIO_ctrl : Z := 0x236dbc.
Definition SITE_bc_ctrl : Z := 0x236f94.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition bc_frame (s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition bc_s0_post (sp gp tp t0 t2 a5 a7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' : word) (BI cmd larg parg lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t1x a6x : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bc_ctrl) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1x t2 sp (Z_to_bv 64 larg) (Z_to_bv 64 BI) (Z_to_bv 64 cmd) (Z_to_bv 64 larg) (Z_to_bv 64 parg)
                 (Z_to_bv 64 e_mem_ctrl) a5 a6x a7 (Z_to_bv 64 parg) (Z_to_bv 64 cmd) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 24)) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (BI + 8)) (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_mem_ctrl) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) (bc_frame s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma bc_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI cmd larg parg meth : Z),
  (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BI (bio_head meth) -> acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  ro_cells asegs m ((meth + 64) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  0 <= cmd < 2^64 -> 0 <= larg < 2^64 -> 0 <= parg < 2^64 -> mem_inv asegs m ->
  evt asegs (bc_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t2 a5 a7 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' BI cmd larg parg lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 cmd) (Z_to_bv 64 larg) (Z_to_bv 64 parg) a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BIO_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros until meth. intros HM HLO HLOS SPH ST UT SHC BH ACCBI BI0 BIAL BIHI BILO MSB HC HL HP MI.
  unfold e_BIO_ctrl, g_shadow_memory_dynamic_address, bio_head in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 96, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 96, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  { replace ((5538432 + 64) / 8 + 2147450880) with 2148143192 in MSB by reflexivity.
    th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
    zstep. do 12 zstep. zstep.
    zstep. if_cases Ka; zify_cond Ka; try (exfalso; rewrite ?unsigned_lit in Ka by lia; lia). try clear Ka.
    zstep.
    zstep. zstep. zstep.
    zstep. do 3 zstep. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep.
    do 4 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep. do 3 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. zstep. zstep. zstep. th_if_lit.
    do 3 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep. cbv beta. zstep. th_if_lit.
    zstep.
    do 4 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. zstep. zstep. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold bc_s0_post, SITE_bc_ctrl, e_mem_ctrl, bc_frame. apply evt_done. exists t1. do 2 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR | assumption]. }
  { replace ((5538592 + 64) / 8 + 2147450880) with 2148143212 in MSB by reflexivity.
    th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
    zstep. do 12 zstep. zstep.
    zstep. if_cases Ka; zify_cond Ka; try (exfalso; rewrite ?unsigned_lit in Ka by lia; lia). try clear Ka.
    zstep.
    zstep. zstep. zstep.
    zstep. do 3 zstep. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep.
    do 4 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep. do 3 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. zstep. zstep. zstep. th_if_lit.
    do 3 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep. cbv beta. zstep. th_if_lit.
    zstep.
    do 4 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. zstep. zstep. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold bc_s0_post, SITE_bc_ctrl, e_mem_ctrl, bc_frame. apply evt_done. exists t1. do 2 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR | assumption]. }
Qed.

(* [comment removed for export] *)
Definition bc_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 : word) (F : bvmap 5 word) (fc : bv 32) (v : word) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' v a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma bc_s1_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' v a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 (s1x s2x s3x : word)
    (F : bvmap 5 word) fc (m : mem) (lo BI meth : Z),
  (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -96) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -96) (bc_frame s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BI (bio_head meth) -> acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo -> mem_inv asegs m ->
  evt asegs (bc_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 F fc v lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1x v a1 a2 a3 a4 a5 a6 a7 s2x s3x (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 24)) (Z_to_bv 64 (BI + 16))
             (Z_to_bv 64 (BI + 8)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bc_ctrl) fc None m (seg_rom asegs)).
Proof.
  intros until meth. intros HM HLO HLOS SPH ST UT FR BH ACCBI BI0 BIAL BIHI BILO MI.
  unfold SITE_bc_ctrl, bio_head, bc_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -96)) = SP + -96) by (apply unsigned_lit; lia).
  destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  { zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. zstep. th_if_lit.
    do 3 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep. do 12 zstep. zstep. th_release FR SP. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold bc_s1_post. apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; assumption. }
  { zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. zstep. th_if_lit.
    do 3 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep. do 12 zstep. zstep. th_release FR SP. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold bc_s1_post. apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; assumption. }
Qed.

Section CBctrl.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
(* [comment removed for export] *)
Hypothesis GO_memmeth : GOBJ MEM_METHOD 112.
(* [comment removed for export] *)
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.

Lemma memmeth_ctrl_sh : forall (Σ : rts RT) (m : mem), ART RT Σ m -> ro_cells asegs m ((MEM_METHOD + 64) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros Σ m HA. pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (MEM_METHOD + 64) HA GO_memmeth ltac:(unfold MEM_METHOD; lia) ltac:(unfold MEM_METHOD; lia) ltac:(reflexivity)) as X.
  cbn [Z.ltb Z.sub Z.add Z.leb MEM_METHOD] in X. exact X.
Qed.

Lemma meth_ctrl_sh : forall meth (Σ : rts RT) (m : mem), (meth = M_MEM_A \/ meth = M_SECMEM_A) -> ART RT Σ m ->
  ro_cells asegs m ((meth + 64) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros meth Σ m [-> | ->] HA.
  - exact (memmeth_ctrl_sh Σ m HA).
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_SECMEM_A + 64) HA GO_secmeth ltac:(unfold M_SECMEM_A; lia) ltac:(unfold M_SECMEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_SECMEM_A] in X. exact X.
Qed.

(* [comment removed for export] *)
Definition bio_ctrl_info_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len off fl larg meth : Z) (iw shw rrw numw padw rmaxw rflw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 3 -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 0 ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) ->
  rw_cells asegs m (BI + 40) (bio_w1_cells iw shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) -> 0 <= larg < 2 ^ 64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 96 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_ctrl m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (len - off)) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m')).

Theorem bio_ctrl_info_cps : bio_ctrl_info_stmt.
Proof.
  pose proof (ctrl_info_cps RT AF GOBJ AFP) as C_CI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len off fl larg meth iw shw rrw numw padw rmaxw rflw
    FDO MST -> -> -> -> -> INBI BIAL HM BH BW FLOK INBB BBAL BBC INBM BMAL INR RAL RC HLA ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -96).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  (* [comment removed for export] *)
  pose proof (bc_s0_walk ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI 3 larg 0 meth
                HM HLO1 HLOS SPH ST UT SHC BH ACCBI BI0 BIAL BIHI BILO (meth_ctrl_sh meth Σ m HM ART0) ltac:(clear; lia) HLA ltac:(clear; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1x & a6x & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AGL : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m m1) by (intros a' n H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 6. }
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells iw shw fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]. }
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [apply AGL; cbn [cells_size csize Nat.add]; exact BBLO | exact WM1]. }
  assert (RC1 : rw_cells asegs m1 R (readp_cells len D off rmaxw rflw)).
  { apply (rw_cells_agree asegs m m1 _ _ RC); [apply AGL; unfold readp_cells; cbn [cells_size csize Nat.add]; exact RLO | exact WM1]. }
  (* [comment removed for export] *)
  apply (C_CI Σ PMc (Z_to_bv 64 SITE_bc_ctrl) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1x t2 sp (Z_to_bv 64 larg) (Z_to_bv 64 BI) (Z_to_bv 64 3) (Z_to_bv 64 larg) (Z_to_bv 64 0)
           (Z_to_bv 64 e_mem_ctrl) a5 a6x a7 (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 24)) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (BI + 8)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6
           F fc m1 lo BI BB BM R D len off fl iw shw rrw numw padw rmaxw rflw FDO MST eq_refl eq_refl eq_refl eq_refl INBI BIAL BW1 FLOK INBB BBAL BBC1 INBM BMAL INR RAL RC1 ART1 MI1 CO1).
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_bc_ctrl) in Hc2' by (unfold SITE_bc_ctrl; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x) -> m2 x = m1 x) by (intros x Hx; exact (PRES2 x Hx)).
  assert (FR2 : rw_cells asegs m2 usp1 (bc_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold bc_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2. left. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (BH2 : rw_cells asegs m2 BI (bio_head meth)).
  { apply (rw_cells_agree_nw asegs m m2 _ _ BH). intros x Hx. cbv beta in Hx. unfold bio_head in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (P2 x ltac:(apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia])). apply AGL with (a := BI) (n := 128); [exact BILO | cbv beta; clear - Hx; lia]. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (bc_s1_walk ra (Z_to_bv 64 SITE_bc_ctrl) sp gp y0 y1 y2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (len - off)) h1 h2 h3 h4 h5 h6 h7 s11 y3 y4 y5 y6
                (Z_to_bv 64 larg) (Z_to_bv 64 0) (Z_to_bv 64 3) F2 fc2 m2 lo BI meth HM HLO1 HLOS SPH ST2 UT2 FR2 BH2 (proj2 (af_acc_live RT AF Σ m2 BI 128 ART2 INBI)) BI0 BIAL BIHI BILO MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  apply Hk. eapply ASTA_conseq; [exact Hc3|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
  fold usp in ST3. exists m3. split; [do 16 eexists; reflexivity|].
  assert (E3 : forall x : word, m3 x = m2 x) by (intros x; apply MU3; exact I).
  assert (ART3 : ART RT Σ m3) by (apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; clear - NUM; lia)); [intros x _; apply E3 | exact WM3]).
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  intros x Hx. rewrite E3, (P2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia])). apply PR1; [exact Hx | exact I].
Qed.

(* [comment removed for export] *)
Definition bio_ctrl_ptr_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl iw PP larg meth : Z) (shw rrw numw padw rmaxw flw oldpp : word) (junk : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 PP ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max flw) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw flw) -> BM <> R ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> BB -> D <> BM -> D <> R ->
  0 <= off <= len -> len <= max -> 0 < max < 2 ^ 31 -> length junk = Z.to_nat max -> rw_cells asegs m D [CB (Z.to_nat max) junk] ->
  PP mod 8 = 0 -> rw_cells asegs m PP [C8 oldpp] -> pp_loc (rt_frames RT Σ) m (bv_unsigned sp) PP -> 0 <= larg < 2 ^ 64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 240 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_ctrl m)))
    (ASTA RT Σ PMc (fun ms => exists (rmaxw' : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (CP_W BM R D max PP) m m'
        /\ rw_cells asegs m' BM (bufmem_cells (len - off) D max flw) /\ rw_cells asegs m' R (readp_cells (len - off) D 0 rmaxw' flw)
        /\ rw_cells asegs m' D [CB (Z.to_nat max) (mv_cur (Z.to_nat off) junk (Z.to_nat (len - off)))]
        /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 BM)])).

Theorem bio_ctrl_ptr_cps : bio_ctrl_ptr_stmt.
Proof.
  pose proof (ctrl_ptr_cps RT AF GOBJ AFP MMV) as C_CP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl iw PP larg meth shw rrw numw padw rmaxw flw oldpp junk
    FDO MST -> -> -> -> -> INBI BIAL HM BH BW FLOK HIW INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR IND NDBI NDBB NDBM NDR HOFF HLEN HMAX LJ DC PPAL PPC LOC HLA ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -96).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI.
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _). assert (DLO : D + max <= lo) by (clear - DLO' LOW; lia). clear DLO'.
  destruct (pp_facts RT AF Σ m usp lo PP ART0 LOC PPAL LOW LOR SPT) as (PP0 & PPHI & PPUT & PPSH & PPSEP & PPA & PPAP & PPACC).
  (* [comment removed for export] *)
  pose proof (bc_s0_walk ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI 115 larg PP meth
                HM HLO1 HLOS SPH ST UT SHC BH ACCBI BI0 BIAL BIHI BILO (meth_ctrl_sh meth Σ m HM ART0) ltac:(clear; lia) HLA ltac:(clear - PP0 PPHI; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1x & a6x & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x) by (intros x Hx; apply PR1; [exact Hx | exact I]).
  assert (AGL : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m m1) by (intros a' n H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 6. }
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]. }
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [apply AGL; cbn [cells_size csize Nat.add]; exact BBLO | exact WM1]. }
  assert (BMC1 : rw_cells asegs m1 BM (bufmem_cells len D max flw)).
  { apply (rw_cells_agree asegs m m1 _ _ BMC); [apply AGL; unfold bufmem_cells; cbn [cells_size csize Nat.add]; exact BMLO | exact WM1]. }
  assert (RC1 : rw_cells asegs m1 R (readp_cells len D off rmaxw flw)).
  { apply (rw_cells_agree asegs m m1 _ _ RC); [apply AGL; unfold readp_cells; cbn [cells_size csize Nat.add]; exact RLO | exact WM1]. }
  assert (DC1 : rw_cells asegs m1 D [CB (Z.to_nat max) junk]).
  { apply (rw_cells_agree asegs m m1 _ _ DC); [apply AGL; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact DLO | exact WM1]. }
  assert (PPC1 : rw_cells asegs m1 PP [C8 oldpp]).
  { apply (rw_cells_agree asegs m m1 _ _ PPC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1. replace (bv_unsigned x) with (PP + (bv_unsigned x - PP)) by (clear; lia). apply PPA. clear - Hx. lia. }
  assert (LOC1 : pp_loc (rt_frames RT Σ) m1 (bv_unsigned (Z_to_bv 64 usp1)) PP).
  { rewrite EU1. destruct LOC as [(L1 & L2) | (f & k & Hin & L1 & L2 & SHZ)]; [left; unfold usp1; clear - L1 L2; lia | right].
    exists f, k. split; [exact Hin|]. split; [exact L1|]. split; [exact L2|].
    apply (bytes_at_agree asegs m m1 _ _ SHZ). intros a Ha. cbv beta in Ha. cbn [length Z.of_nat Pos.of_succ_nat] in Ha. apply MU1. cbn [outside]. split; [| exact I].
    unfold shad, SHB in Ha. assert (PP / 8 <= 2 ^ 44 - 1) by (clear - PPHI PP0; Z.div_mod_to_equations; lia). clear - Ha H HLO1 HLOS. lia. }
  (* [comment removed for export] *)
  apply (C_CP Σ PMc (Z_to_bv 64 SITE_bc_ctrl) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1x t2 sp (Z_to_bv 64 larg) (Z_to_bv 64 BI) (Z_to_bv 64 115) (Z_to_bv 64 larg) (Z_to_bv 64 PP)
           (Z_to_bv 64 e_mem_ctrl) a5 a6x a7 (Z_to_bv 64 PP) (Z_to_bv 64 115) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 24)) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (BI + 8)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6
           F fc m1 lo BI BB BM R D len max off fl iw PP shw rrw numw padw rmaxw flw oldpp junk
           FDO MST eq_refl eq_refl eq_refl eq_refl INBI BIAL BW1 FLOK HIW INBB BBAL BBC1 INBM BMAL BMC1 INR RAL RC1 NMR IND NDBB NDBM NDR HOFF HLEN HMAX LJ DC1 PPAL PPC1 LOC1 ART1 MI1 CO1
           ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia)).
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (rmaxw2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BMC2 & RC2 & DC2 & PPC2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_bc_ctrl) in Hc2' by (unfold SITE_bc_ctrl; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x) -> outside (CP_W BM R D max PP) (bv_unsigned x) -> m2 x = m1 x) by (intros x Hx Ho; exact (PRES2 x Hx Ho)).
  assert (FR2 : rw_cells asegs m2 usp1 (bc_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold bc_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold CP_W; cbn [outside]; unfold usp1 in *; clear - Hx BMLO RLO DLO HLO1 PPSEP; lia]. }
  assert (BH2 : rw_cells asegs m2 BI (bio_head meth)).
  { apply (rw_cells_agree_nw asegs m m2 _ _ BH). intros x Hx. cbv beta in Hx. unfold bio_head in Hx. cbn [cells_size csize Nat.add] in Hx.
    pose proof (live_ne_apart RT AF Σ m BI 128 BM 32 ART0 INBI INBM ltac:(intros E; injection E; lia)) as A1.
    pose proof (live_ne_apart RT AF Σ m BI 128 R 32 ART0 INBI INR ltac:(intros E; injection E; lia)) as A2.
    pose proof (live_ne_apart RT AF Σ m BI 128 D max ART0 INBI IND ltac:(intros E; injection E; intros _ E1; exact (NDBI (eq_sym E1)))) as A3. pose proof (PPAP BI 128 INBI) as A4.
    rewrite (P2 x ltac:(apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia]) ltac:(unfold CP_W; cbn [outside]; clear - Hx A1 A2 A3 A4; lia)).
    apply AGL with (a := BI) (n := 128); [exact BILO | cbv beta; clear - Hx; lia]. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (bc_s1_walk ra (Z_to_bv 64 SITE_bc_ctrl) sp gp y0 y1 y2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 1) h1 h2 h3 h4 h5 h6 h7 s11 y3 y4 y5 y6
                (Z_to_bv 64 larg) (Z_to_bv 64 PP) (Z_to_bv 64 115) F2 fc2 m2 lo BI meth HM HLO1 HLOS SPH ST2 UT2 FR2 BH2 (proj2 (af_acc_live RT AF Σ m2 BI 128 ART2 INBI)) BI0 BIAL BIHI BILO MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  apply Hk. eapply ASTA_conseq; [exact Hc3|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
  fold usp in ST3. exists rmaxw2, m3. split; [do 16 eexists; reflexivity|].
  assert (E3 : forall x : word, m3 x = m2 x) by (intros x; apply MU3; exact I).
  assert (ART3 : ART RT Σ m3) by (apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; clear - NUM; lia)); [intros x _; apply E3 | exact WM3]).
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  split; [intros x Hx Ho; rewrite E3, (P2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) Ho); exact (P1 x Hx)|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ BMC2); [intros x _; apply E3 | exact WM3]|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ RC2); [intros x _; apply E3 | exact WM3]|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ DC2); [intros x _; apply E3 | exact WM3]|].
  apply (rw_cells_agree asegs m2 m3 _ _ PPC2); [intros x _; apply E3 | exact WM3].
Qed.
(* [comment removed for export] *)
Definition bio_ctrl_ptr_same_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R fl iw PP larg meth : Z) (shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 115 -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 PP ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl -> 0 < iw < 2 ^ 31 ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM [C8 lw; C8 dw; C8 mw; C8 flw] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R [C8 rlw; C8 dw; C8 rmw; C8 rflw] ->
  PP mod 8 = 0 -> rw_cells asegs m PP [C8 oldpp] -> pp_loc (rt_frames RT Σ) m (bv_unsigned sp) PP -> 0 <= larg < 2 ^ 64 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 240 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_ctrl m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(PP, PP + 8)] m m'
        /\ rw_cells asegs m' PP [C8 (Z_to_bv 64 BM)])).

Theorem bio_ctrl_ptr_same_cps : bio_ctrl_ptr_same_stmt.
Proof.
  pose proof (ctrl_ptr_same_cps RT AF GOBJ AFP) as C_CP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R fl iw PP larg meth shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp
    FDO MST -> -> -> -> -> INBI BIAL HM BH BW FLOK HIW INBB BBAL BBC INBM BMAL BMC INR RAL RC PPAL PPC LOC HLA ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -96).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as (BM0 & BMLO' & _). assert (BMLO : BM + 32 <= lo) by (clear - BMLO' LOW; lia). clear BMLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BM 32 ART0 INBM ltac:(lia)) as BMHI.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI.
  destruct (pp_facts RT AF Σ m usp lo PP ART0 LOC PPAL LOW LOR SPT) as (PP0 & PPHI & PPUT & PPSH & PPSEP & PPA & PPAP & PPACC).
  (* [comment removed for export] *)
  pose proof (bc_s0_walk ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI 115 larg PP meth
                HM HLO1 HLOS SPH ST UT SHC BH ACCBI BI0 BIAL BIHI BILO (meth_ctrl_sh meth Σ m HM ART0) ltac:(clear; lia) HLA ltac:(clear - PP0 PPHI; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (t1x & a6x & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x) by (intros x Hx; apply PR1; [exact Hx | exact I]).
  assert (AGL : forall a n, a + n <= lo -> agree_on (fun x => a <= x < a + n) m m1) by (intros a' n H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 6. }
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 iw) shw fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]. }
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [apply AGL; cbn [cells_size csize Nat.add]; exact BBLO | exact WM1]. }
  assert (BMC1 : rw_cells asegs m1 BM [C8 lw; C8 dw; C8 mw; C8 flw]).
  { apply (rw_cells_agree asegs m m1 _ _ BMC); [apply AGL; cbn [cells_size csize Nat.add]; exact BMLO | exact WM1]. }
  assert (RC1 : rw_cells asegs m1 R [C8 rlw; C8 dw; C8 rmw; C8 rflw]).
  { apply (rw_cells_agree asegs m m1 _ _ RC); [apply AGL; cbn [cells_size csize Nat.add]; exact RLO | exact WM1]. }
  assert (PPC1 : rw_cells asegs m1 PP [C8 oldpp]).
  { apply (rw_cells_agree asegs m m1 _ _ PPC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1. replace (bv_unsigned x) with (PP + (bv_unsigned x - PP)) by (clear; lia). apply PPA. clear - Hx. lia. }
  assert (LOC1 : pp_loc (rt_frames RT Σ) m1 (bv_unsigned (Z_to_bv 64 usp1)) PP).
  { rewrite EU1. destruct LOC as [(L1 & L2) | (f & k & Hin & L1 & L2 & SHZ)]; [left; unfold usp1; clear - L1 L2; lia | right].
    exists f, k. split; [exact Hin|]. split; [exact L1|]. split; [exact L2|].
    apply (bytes_at_agree asegs m m1 _ _ SHZ). intros a Ha. cbv beta in Ha. cbn [length Z.of_nat Pos.of_succ_nat] in Ha. apply MU1. cbn [outside]. split; [| exact I].
    unfold shad, SHB in Ha. assert (PP / 8 <= 2 ^ 44 - 1) by (clear - PPHI PP0; Z.div_mod_to_equations; lia). clear - Ha H HLO1 HLOS. lia. }
  (* [comment removed for export] *)
  apply (C_CP Σ PMc (Z_to_bv 64 SITE_bc_ctrl) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1x t2 sp (Z_to_bv 64 larg) (Z_to_bv 64 BI) (Z_to_bv 64 115) (Z_to_bv 64 larg) (Z_to_bv 64 PP)
           (Z_to_bv 64 e_mem_ctrl) a5 a6x a7 (Z_to_bv 64 PP) (Z_to_bv 64 115) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 24)) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (BI + 8)) (Z_to_bv 64 0x7fff8000)
           (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6
           F fc m1 lo BI BB BM R fl iw PP shw rrw numw padw lw dw mw flw rlw rmw rflw oldpp
           FDO MST eq_refl eq_refl eq_refl eq_refl INBI BIAL BW1 FLOK HIW INBB BBAL BBC1 INBM BMAL BMC1 INR RAL RC1 PPAL PPC1 LOC1 ART1 MI1 CO1
           ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia)).
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & PPC2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_bc_ctrl) in Hc2' by (unfold SITE_bc_ctrl; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x) -> outside [(PP, PP + 8)] (bv_unsigned x) -> m2 x = m1 x) by (intros x Hx Ho; exact (PRES2 x Hx Ho)).
  assert (FR2 : rw_cells asegs m2 usp1 (bc_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold bc_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | cbn [outside]; unfold usp1 in *; clear - Hx HLO1 PPSEP; lia]. }
  assert (BH2 : rw_cells asegs m2 BI (bio_head meth)).
  { apply (rw_cells_agree_nw asegs m m2 _ _ BH). intros x Hx. cbv beta in Hx. unfold bio_head in Hx. cbn [cells_size csize Nat.add] in Hx.
    pose proof (PPAP BI 128 INBI) as A4.
    rewrite (P2 x ltac:(apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia]) ltac:(cbn [outside]; clear - Hx A4; lia)).
    apply AGL with (a := BI) (n := 128); [exact BILO | cbv beta; clear - Hx; lia]. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (bc_s1_walk ra (Z_to_bv 64 SITE_bc_ctrl) sp gp y0 y1 y2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 1) h1 h2 h3 h4 h5 h6 h7 s11 y3 y4 y5 y6
                (Z_to_bv 64 larg) (Z_to_bv 64 PP) (Z_to_bv 64 115) F2 fc2 m2 lo BI meth HM HLO1 HLOS SPH ST2 UT2 FR2 BH2 (proj2 (af_acc_live RT AF Σ m2 BI 128 ART2 INBI)) BI0 BIAL BIHI BILO MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  apply Hk. eapply ASTA_conseq; [exact Hc3|]. intros ms (q0 & q1 & q2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & q3 & q4 & q5 & q6 & m3 & -> & MU3 & WM3 & MI3 & ST3).
  fold usp in ST3. exists m3. split; [do 16 eexists; reflexivity|].
  assert (E3 : forall x : word, m3 x = m2 x) by (intros x; apply MU3; exact I).
  assert (ART3 : ART RT Σ m3) by (apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; clear - NUM; lia)); [intros x _; apply E3 | exact WM3]).
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  split; [intros x Hx Ho; rewrite E3, (P2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) Ho); exact (P1 x Hx)|].
  apply (rw_cells_agree asegs m2 m3 _ _ PPC2); [intros x _; apply E3 | exact WM3].
Qed.
End CBctrl.
