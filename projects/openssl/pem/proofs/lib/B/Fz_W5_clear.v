(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_M_malloc Fz_env Fz_M_free Fz_T_sa Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Fz_W5_rep Fz_I3_eclw.
From OSSVerify.Proofs.openssl.pem.lib.B Require Export Fz_W5_agr Fz_W5_eclr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Definition e_ERR_clear_error : Z := 0x1f9330.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition CLR_SITES : list (Z * Z) := ECL_SITES.
Definition CLR_CALLS : list (Z * Z) := ECL_CALLS.

(* [comment removed for export] *)
Definition clr_head_st (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E i : Z) (m : mem)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 i) (Z_to_bv 64 SHB) (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 ECL_LOOP) fc None m (seg_rom bsegs).

(* [comment removed for export] *)
Lemma es_rep_set_tb : forall (m m' : mem) E top bot fl mk buf fs ls fn, es_rep m E top bot fl mk buf fs ls fn ->
  munch [(E + 896, E + 904)] m m' -> wmono bsegs m m' -> rw_cells bsegs m' (E + 896) [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  es_rep m' E 0 0 fl mk buf fs ls fn.
Proof.
  intros m m' E top bot fl mk buf fs ls fn R MU WM TB'.
  destruct R as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  assert (AGs : forall (P : Z -> Prop), (forall x, P x -> E <= x < E + 896) -> agree_on P m m').
  { intros P HP x Hx. apply MU. cbn [outside]. pose proof (HP _ Hx). lia. }
  unfold es_rep.
  split; [apply (u32arr_agree m m' _ _ A1); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L1 in Hx; lia | exact WM]|]. split; [exact L1|].
  split; [apply (u32arr_agree m m' _ _ A2); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L2 in Hx; lia | exact WM]|]. split; [exact L2|].
  split; [apply (u64arr_agree m m' _ _ A3); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L3 in Hx; lia | exact WM]|]. split; [exact L3|].
  split; [apply (u8arr_agree m m' _ _ A4); [apply AGs; intros x Hx; cbv beta in Hx; rewrite repeat_length in Hx; lia | exact WM]|].
  split; [apply (u8arr_agree m m' _ _ A5); [apply AGs; intros x Hx; cbv beta in Hx; rewrite repeat_length in Hx; lia | exact WM]|].
  split; [apply (u8arr_agree m m' _ _ A6); [apply AGs; intros x Hx; cbv beta in Hx; rewrite repeat_length in Hx; lia | exact WM]|].
  split; [apply (u64arr_agree m m' _ _ A7); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L7 in Hx; lia | exact WM]|]. split; [exact L7|].
  split; [apply (u32arr_agree m m' _ _ A8); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L8 in Hx; lia | exact WM]|]. split; [exact L8|].
  split; [apply (u64arr_agree m m' _ _ A9); [apply AGs; intros x Hx; cbv beta in Hx; rewrite L9 in Hx; lia | exact WM]|]. split; [exact L9|].
  split; [exact TB'|]. lia.
Qed.

Section CClr.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_GSI0 : get_state_steady0_stmt RT.
Hypothesis C_FRN : crypto_free_null_env_stmt RT.
Hypothesis C_FRC : crypto_free_env_stmt RT.

Definition ERRBAD (MK SA NODES E : Z) : list Z := [E; MK; SA; NODES].
Definition clr_frame (rac s0c s1c s2c s3c s4c : word) : list cell := [C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].

(* [comment removed for export] *)
Definition clr_iter_stmt : Prop :=
  forall (Σ : rts RT) PMc (sp gp s5 s6 s7 s8 s9 s10 s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem) (lo : Z) (outer : list Z)
    (rac s0c s1c s2c s3c s4c : word) (MK SA NODES E : Z) (i top bot : Z) (fl mk buf fs ls fn : list word) (wf wn : word) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m (Z_to_bv 64 (bv_unsigned sp + -48)) lo -> lo + RT_STACK + 96 <= bv_unsigned sp - 48 ->
  rt_sp0 RT Σ - STACK_WIN <= bv_unsigned sp - 48 -> bv_unsigned sp + 16 <= USTACK_TOP ->
  cg_ctx (rt_cg RT Σ) e_ERR_clear_error (bv_unsigned rac :: outer) -> uw_chain m sp s0c outer -> cg_has (rt_cg RT Σ) CLR_SITES CLR_CALLS ->
  rw_cells bsegs m (bv_unsigned sp + -48) (clr_frame rac s0c s1c s2c s3c s4c) ->
  err_blocks (rt_live RT Σ) MK SA NODES E -> es_rep m E top bot fl mk buf fs ls fn -> 0 <= i < 16 ->
  nth_error fs (Z.to_nat i) = Some wf -> nth_error fn (Z.to_nat i) = Some wn ->
  slot_free_ok (rt_live RT Σ) (ERRBAD MK SA NODES E) wf -> slot_free_ok (rt_live RT Σ) (ERRBAD MK SA NODES E) wn -> (bv_unsigned wf <> 0 -> bv_unsigned wf <> bv_unsigned wn) ->
  cl_env m lb canary ->
  cps bsegs (ASTA RT Σ PMc (eq (clr_head_st sp gp (Z_to_bv 64 0xbd66f0) s5 s6 s7 s8 s9 s10 s11 F fc E i m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)))
    (fun c => exists (Σ' : rts RT) (fl' mk' buf' ls' : list word),
       ASTA RT Σ' PMc (fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
           ms = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xbd66f0) t0' t1' t2' sp (Z_to_bv 64 E) a0' a1' a2' a3' a4' a5' a6' a7'
                        (Z_to_bv 64 (i + 1)) (Z_to_bv 64 SHB) (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (Z_to_bv 64 (ecl_next i)) fc' None m' (seg_rom bsegs)
           /\ ART RT Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -48)
           /\ rw_cells bsegs m' (bv_unsigned sp + -48) (clr_frame rac s0c s1c s2c s3c s4c)
           /\ es_rep m' E top bot fl' mk' buf' (upd fs (Z.to_nat i) (Z_to_bv 64 0)) ls' (upd fn (Z.to_nat i) (Z_to_bv 64 0)) /\ cl_env m' lb canary /\ uw_chain m' sp s0c outer
           /\ (forall x : word, aclient (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m' x = m x)) c
       /\ rt_live RT Σ' = rmw wn (rmw wf (rt_live RT Σ)) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

Lemma clr_iter_cps : clr_iter_stmt.
Proof.
  intros Σ PMc sp gp s5 s6 s7 s8 s9 s10 s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m lo outer rac s0c s1c s2c s3c s4c MK SA NODES E i top bot fl mk buf fs ls fn wf wn lb canary
    FDO MST ART0 MI0 CALL HSTK LOW1 SPT CTX UWC CGH FR BLK ES HI FSI FNI SOKF SOKN DIS CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT1 & SPA1).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *. set (usp1 := usp + -48) in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - LOW1 SPT SP0W; lia).
  rewrite EU1 in ST, LOR, SPT1, SPA1.
  pose proof BLK as (INM & INS & INN & INE & MKAL & SAAL & NAL & EAL).
  pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as (R4a & R4 & _).
  assert (ELO : E + 904 <= lo) by (clear - R4 LOW; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  pose proof (ecl_wcall (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xbd66f0) t0 t1 t2 sp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m E i UT) as W1.
  unfold clr_head_st in HA. fold usp in HA. fold usp1 in HA.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & <- & Hc1'). clear Hc1.
  assert (FRR : rw_cells bsegs m (usp - 16) [C8 s0c; C8 rac]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s4c; C8 s3c; C8 s2c; C8 s1c])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m usp1 [C8 s4c; C8 s3c; C8 s2c; C8 s1c] [C8 s0c; C8 rac] FR). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ERR_clear_error e_err_clear SITE_ecl_call m m rac s0c sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC ltac:(intros x Hx; reflexivity) FRR ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  assert (CGE : cg_has (rt_cg RT Σ) ECR_SITES ECR_CALLS).
  { split; intros e He; [apply (proj1 CGH) | apply (proj2 CGH)]; unfold CLR_SITES, CLR_CALLS, ECL_SITES, ECL_CALLS, ECR_SITES, ECR_CALLS in *; cbn [In] in *; tauto. }
  (* [comment removed for export] *)
  apply (err_clear_cps RT AF GOBJ AFP C_FRN C_FRC Σ PMc (Z_to_bv 64 SITE_ecl_call) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xbd66f0) t0 t1 t2 sp (Z_to_bv 64 E) (Z_to_bv 64 E) (Z_to_bv 64 i) (Z_to_bv 64 0)
           a3 a4 a5 a6 a7 (Z_to_bv 64 i) (Z_to_bv 64 SHB) (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo (bv_unsigned rac :: outer) (ERRBAD MK SA NODES E)
           E i top bot fl mk buf fs ls fn wf wn lb canary FDO MST eq_refl eq_refl eq_refl ART0 MI0).
  { unfold call_ok. rewrite EU1. exact (conj ST (conj LOW (conj LOR (conj SPT1 SPA1)))). }
  { rewrite EU1. unfold usp1. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_ecl_call) by (unfold SITE_ecl_call; lia). exact CTX1. }
  { exact UWC1. } { exact CGE. } { exact INE. } { exact EAL. } { left; reflexivity. } { exact ES. } { exact HI. } { exact FSI. } { exact FNI. } { exact SOKF. } { exact SOKN. } { exact DIS. } { exact CLE. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & v1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & _ & PRES2 & ES2 & CLE2) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ecl_call) in Hc2' by (unfold SITE_ecl_call; lia).
  assert (A02 : forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ) usp1 (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m2 x = m x).
  { intros x Hx HnE. apply (PRES2 x Hx). unfold ECR_W. cbn [outside]. clear - HnE. lia. }
  assert (FR2 : rw_cells bsegs m2 usp1 (clr_frame rac s0c s1c s2c s3c s4c)).
  { apply (rw_cells_agree_nw bsegs m m2 _ _ FR). intros x Hx. cbv beta in Hx. unfold clr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A02; [left; unfold usp1, USTACK_TOP in *; clear - Hx SPT; lia | unfold usp1, RT_STACK in *; clear - Hx ELO LOR; lia]. }
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2).
  { intros x Hx. cbv beta in Hx. apply A02; [left; unfold usp1; clear - Hx; lia | unfold usp1, RT_STACK in *; clear - Hx ELO LOR; lia]. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (ecl_wnext (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xbd66f0) w0 w1 w2 sp v1 g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 (Z_to_bv 64 SITE_ecl_call) F2 fc2 m2 E i HI UT2) as W2.
  cl_lift W2 Hc2' c3 Hc3.
  apply Hk. exists Σ1. do 4 eexists.
  split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 CG1))))].
  eapply ASTA_conseq; [exact Hc3|]. intros ms <-.
  exists (Z_to_bv 64 SITE_ecl_call), w0, w1, w2, v1, g1, g2, g3, g4, g5, g6, g7, w3, w4, w5, w6, F2, fc2, m2.
  fold usp. fold usp1.
  split; [reflexivity|]. split; [exact ART2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact FR2|]. split; [exact ES2|]. split; [exact CLE2|].
  split; [exact (uw_chain_agree outer m m2 sp s0c UWC AG02)|].
  intros x Hx HnE. apply A02; [| exact HnE]. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia].
Qed.

Definition selw (fs fn : list word) (b : bool) (j : Z) : option word := nth_error (if b then fn else fs) (Z.to_nat j).

(* [comment removed for export] *)
Definition clr_loop_stmt (i : Z) : Prop :=
  forall (Σ : rts RT) PMc (sp gp s5 s6 s7 s8 s9 s10 s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem) (lo : Z) (outer : list Z)
    (rac s0c s1c s2c s3c s4c : word) (MK SA NODES E : Z) (top bot : Z) (fl mk buf fs ls fn : list word) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m (Z_to_bv 64 (bv_unsigned sp + -48)) lo -> lo + RT_STACK + 96 <= bv_unsigned sp - 48 -> rt_sp0 RT Σ - STACK_WIN <= bv_unsigned sp - 48 -> bv_unsigned sp + 16 <= USTACK_TOP ->
  cg_ctx (rt_cg RT Σ) e_ERR_clear_error (bv_unsigned rac :: outer) -> uw_chain m sp s0c outer -> cg_has (rt_cg RT Σ) CLR_SITES CLR_CALLS ->
  rw_cells bsegs m (bv_unsigned sp + -48) (clr_frame rac s0c s1c s2c s3c s4c) ->
  err_blocks (rt_live RT Σ) MK SA NODES E -> es_rep m E top bot fl mk buf fs ls fn -> 0 <= i < 16 ->
  (forall b j w, i <= j < 16 -> selw fs fn b j = Some w -> slot_free_ok (rt_live RT Σ) (ERRBAD MK SA NODES E) w) ->
  (forall b1 j1 w1 b2 j2 w2, i <= j1 < 16 -> i <= j2 < 16 -> (b1, j1) <> (b2, j2) -> selw fs fn b1 j1 = Some w1 -> selw fs fn b2 j2 = Some w2 ->
      bv_unsigned w1 <> 0 -> bv_unsigned w1 <> bv_unsigned w2) ->
  cl_env m lb canary ->
  cps bsegs (ASTA RT Σ PMc (eq (clr_head_st sp gp (Z_to_bv 64 0xbd66f0) s5 s6 s7 s8 s9 s10 s11 F fc E i m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)))
    (fun c => exists (Σ' : rts RT) (fl' mk' buf' fs' ls' fn' : list word),
       ASTA RT Σ' PMc (fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
           ms = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xbd66f0) t0' t1' t2' sp (Z_to_bv 64 E) a0' a1' a2' a3' a4' a5' a6' a7'
                        s2' (Z_to_bv 64 SHB) (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F' (Z_to_bv 64 ECL_DONE) fc' None m' (seg_rom bsegs)
           /\ ART RT Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + -48)
           /\ rw_cells bsegs m' (bv_unsigned sp + -48) (clr_frame rac s0c s1c s2c s3c s4c)
           /\ es_rep m' E top bot fl' mk' buf' fs' ls' fn' /\ cl_env m' lb canary
           /\ (forall b j, i <= j < 16 -> selw fs' fn' b j = Some (Z_to_bv 64 0)) /\ (forall b j, 0 <= j < i -> selw fs' fn' b j = selw fs fn b j)
           /\ (forall x : word, aclient (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m' x = m x)) c
       /\ rt_live RT Σ' = clr_rm (combine (skipn (Z.to_nat i) fs) (skipn (Z.to_nat i) fn)) (rt_live RT Σ) /\ err_blocks (rt_live RT Σ') MK SA NODES E
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

Lemma clr_loop : forall k : nat, (k <= 15)%nat -> clr_loop_stmt (15 - Z.of_nat k).
Proof.
  induction k as [|k IH]; intros Hk Σ PMc sp gp s5 s6 s7 s8 s9 s10 s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m lo outer rac s0c s1c s2c s3c s4c
    MK SA NODES E top bot fl mk buf fs ls fn lb canary FDO MST ART0 MI0 CALL HSTK LOW1 SPT CTX UWC CGH FR BLK ES HI SOK DIS CLE T c HA HkT;
    [change (15 - Z.of_nat 0) with 15 in *; set (i := 15) in * | set (i := 15 - Z.of_nat (S k)) in *].
  all: pose proof ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AFS & LFS & _ & _ & AFN & LFN & _).
  all: destruct (nth_error fs (Z.to_nat i)) as [wf|] eqn:FSI; [| exfalso; apply nth_error_None in FSI; lia].
  all: destruct (nth_error fn (Z.to_nat i)) as [wn|] eqn:FNI; [| exfalso; apply nth_error_None in FNI; lia].
  all: apply (clr_iter_cps Σ PMc sp gp s5 s6 s7 s8 s9 s10 s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m lo outer rac s0c s1c s2c s3c s4c
                MK SA NODES E i top bot fl mk buf fs ls fn wf wn lb canary FDO MST ART0 MI0 CALL HSTK LOW1 SPT CTX UWC CGH FR BLK ES HI FSI FNI
                (SOK false i wf ltac:(lia) FSI) (SOK true i wn ltac:(lia) FNI) ltac:(intros NZ; exact (DIS false i wf true i wn ltac:(lia) ltac:(lia) ltac:(congruence) FSI FNI NZ)) CLE T c HA).
  all: intros c1 (Σ1 & fl1 & mk1 & buf1 & ls1 & Hc1 & LV1 & FRS1 & SP1 & CR1 & CG1).
  all: destruct (ASTA_unpack RT Σ1 _ _ c1 Hc1) as (ms1 & (ra' & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & -> & ART1 & MI1 & ST1 & FR1 & ES1 & CLE1 & UWC1 & PV1) & Hc1').
  all: clear Hc1.
  all: assert (BLK1 : err_blocks (rt_live RT Σ1) MK SA NODES E) by (
    destruct BLK as (INM & INS & INN & INE & AL); rewrite LV1;
    assert (KB : forall w L live p n, slot_free_ok L (ERRBAD MK SA NODES E) w -> In p (ERRBAD MK SA NODES E) -> In (p, n) live -> In (p, n) (rmw w live))
      by (intros w L live p n SOKw Hp Hin; destruct SOKw as [Z0 | (_ & NB)]; [unfold rmw; rewrite Z0; exact Hin|]; apply rmw_keep; [exact Hin|]; cbn [fst]; intros EQ; apply NB; rewrite <- EQ; exact Hp);
    pose proof (SOK false i wf ltac:(lia) FSI) as SF; pose proof (SOK true i wn ltac:(lia) FNI) as SN; unfold ERRBAD in *;
    split; [apply (KB wn (rt_live RT Σ)); [exact SN | cbn; tauto | apply (KB wf (rt_live RT Σ)); [exact SF | cbn; tauto | exact INM]]|];
    split; [apply (KB wn (rt_live RT Σ)); [exact SN | cbn; tauto | apply (KB wf (rt_live RT Σ)); [exact SF | cbn; tauto | exact INS]]|];
    split; [apply (KB wn (rt_live RT Σ)); [exact SN | cbn; tauto | apply (KB wf (rt_live RT Σ)); [exact SF | cbn; tauto | exact INN]]|];
    split; [apply (KB wn (rt_live RT Σ)); [exact SN | cbn; tauto | apply (KB wf (rt_live RT Σ)); [exact SF | cbn; tauto | exact INE]] | exact AL]).
  - (* [comment removed for export] *)
    subst i. unfold ecl_next in Hc1'. cbn [Z.eqb Pos.eqb] in Hc1'.
    apply HkT. exists Σ1, fl1, mk1, buf1, (upd fs 15 (Z_to_bv 64 0)), ls1, (upd fn 15 (Z_to_bv 64 0)).
    split.
    2: { split; [| exact (conj BLK1 (conj FRS1 (conj SP1 (conj CR1 CG1))))]. rewrite LV1. change (Z.to_nat 15) with 15%nat in *.
         rewrite (skipn_cons_nth fs 15 wf FSI), (skipn_cons_nth fn 15 wn FNI). rewrite !skipn_all2 by lia. reflexivity. }
    eapply ASTA_conseq; [exact Hc1'|]. intros ms EQ; subst ms.
    exists ra', u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 (15 + 1)), u3, u4, u5, u6, F1, fc1, m1.
    split; [reflexivity|]. split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FR1|]. split; [exact ES1|]. split; [exact CLE1|].
    split; [| split; [| exact PV1]].
    + intros b j Hj. assert (Ej : Z.to_nat j = 15%nat) by lia. unfold selw. rewrite Ej. destruct b; apply nth_error_upd_eq; lia.
    + intros b j Hj. unfold selw. destruct b; apply nth_error_upd_neq; lia.
  - (* [comment removed for export] *)
    unfold ecl_next in Hc1'. replace (i =? 15) with false in Hc1' by (symmetry; apply Z.eqb_neq; lia).
    replace (i + 1) with (15 - Z.of_nat k) in Hc1' by lia.
    assert (SUB1 : forall e, In e (rt_live RT Σ1) -> In e (rt_live RT Σ)) by (rewrite LV1; intros e He; exact (rmw_sub _ _ _ (rmw_sub _ _ _ He))).
    assert (INE1 : In (E, 904) (rt_live RT Σ1)).
    { rewrite LV1. destruct BLK as (_ & _ & _ & INE & _).
      assert (KE : forall w L live, slot_free_ok L (ERRBAD MK SA NODES E) w -> In (E, 904) live -> In (E, 904) (rmw w live)).
      { intros w L live SOKw Hin. destruct SOKw as [Z0 | (_ & NB)]; [unfold rmw; rewrite Z0; exact Hin|]. apply rmw_keep; [exact Hin|]. cbn [fst]. intros EQ. apply NB. left. exact EQ. }
      apply (KE wn (rt_live RT Σ)); [exact (SOK true i wn ltac:(lia) FNI)|]. apply (KE wf (rt_live RT Σ)); [exact (SOK false i wf ltac:(lia) FSI) | exact INE]. }
    assert (CALL1 : call_ok RT Σ1 m1 (Z_to_bv 64 (bv_unsigned sp + -48)) lo).
    { pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
      assert (EU1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; unfold STACK_WIN, USTACK_TOP in *; clear - LOW1 SPT SP0W; lia).
      destruct CALL as (_ & C2 & C3 & C4 & C5). rewrite <- SP1 in C2. unfold call_ok. rewrite EU1 in *. exact (conj ST1 (conj C2 (conj C3 (conj C4 C5)))). }
    rewrite <- CG1 in CTX, CGH. rewrite <- SP1 in LOW1.
    (* [comment removed for export] *)
    assert (SEL1 : forall b j, i + 1 <= j < 16 -> selw (upd fs (Z.to_nat i) (Z_to_bv 64 0)) (upd fn (Z.to_nat i) (Z_to_bv 64 0)) b j = selw fs fn b j).
    { intros b j Hj. unfold selw. destruct b; apply nth_error_upd_neq; lia. }
    assert (SOK1 : forall b j w, 15 - Z.of_nat k <= j < 16 -> selw (upd fs (Z.to_nat i) (Z_to_bv 64 0)) (upd fn (Z.to_nat i) (Z_to_bv 64 0)) b j = Some w ->
                   slot_free_ok (rt_live RT Σ1) (ERRBAD MK SA NODES E) w).
    { intros b j w Hj Hw. rewrite SEL1 in Hw by lia. destruct (SOK b j w ltac:(lia) Hw) as [Z0 | ((n & HIN) & NB)]; [left; exact Z0 | right]. split; [| exact NB]. exists n.
      rewrite LV1. destruct (Z.eq_dec (bv_unsigned w) 0) as [Z0|NZ]; [exfalso; pose proof (af_live_range RT AF Σ m _ _ ART0 HIN) as (P0 & _); lia|].
      apply rmw_keep; [apply rmw_keep; [exact HIN|]|]; cbn [fst].
      - exact (DIS b j w false i wf ltac:(lia) ltac:(lia) ltac:(intros X; injection X; lia) Hw FSI NZ).
      - exact (DIS b j w true i wn ltac:(lia) ltac:(lia) ltac:(intros X; injection X; lia) Hw FNI NZ). }
    assert (DIS1 : forall c1' j1 w1 c2' j2 w2, 15 - Z.of_nat k <= j1 < 16 -> 15 - Z.of_nat k <= j2 < 16 -> (c1', j1) <> (c2', j2) ->
                   selw (upd fs (Z.to_nat i) (Z_to_bv 64 0)) (upd fn (Z.to_nat i) (Z_to_bv 64 0)) c1' j1 = Some w1 ->
                   selw (upd fs (Z.to_nat i) (Z_to_bv 64 0)) (upd fn (Z.to_nat i) (Z_to_bv 64 0)) c2' j2 = Some w2 -> bv_unsigned w1 <> 0 -> bv_unsigned w1 <> bv_unsigned w2).
    { intros c1' j1 w1 c2' j2 w2 H1 H2 NE Hw1 Hw2. rewrite SEL1 in Hw1 by lia. rewrite SEL1 in Hw2 by lia. exact (DIS c1' j1 w1 c2' j2 w2 ltac:(lia) ltac:(lia) NE Hw1 Hw2). }
    apply (IH ltac:(lia) Σ1 PMc sp gp s5 s6 s7 s8 s9 s10 s11 ra' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 m1 lo outer rac s0c s1c s2c s3c s4c
             MK SA NODES E top bot fl1 mk1 buf1 (upd fs (Z.to_nat i) (Z_to_bv 64 0)) ls1 (upd fn (Z.to_nat i) (Z_to_bv 64 0)) lb canary
             FDO MST ART1 MI1 CALL1 HSTK LOW1 SPT CTX UWC1 CGH FR1 BLK1 ES1 ltac:(lia) SOK1 DIS1 CLE1 T c1 Hc1').
    intros c2 (Σ2 & fl2 & mk2 & buf2 & fs2 & ls2 & fn2 & Hc2 & LV2 & BLK2 & FRS2 & SP2 & CR2 & CG2).
    apply HkT. exists Σ2, fl2, mk2, buf2, fs2, ls2, fn2.
    split.
    2: { split; [| exact (conj BLK2 (conj (eq_trans FRS2 FRS1) (conj (eq_trans SP2 SP1) (conj (eq_trans CR2 CR1) (eq_trans CG2 CG1)))))].
         rewrite LV2, LV1. replace (Z.to_nat (15 - Z.of_nat k)) with (S (Z.to_nat i)) by lia.
         rewrite (skipn_upd_lt fs) by lia. rewrite (skipn_upd_lt fn) by lia.
         rewrite (skipn_cons_nth fs (Z.to_nat i) wf FSI), (skipn_cons_nth fn (Z.to_nat i) wn FNI). reflexivity. }
    eapply ASTA_conseq; [exact Hc2|]. intros ms (ra2 & v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & s2x & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> &
                                                    ART2 & MI2 & ST2 & FR2 & ES2 & CLE2 & ZER2 & OLD2 & PV2).
    exists ra2, v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, s2x, v3, v4, v5, v6, F2, fc2, m2.
    split; [reflexivity|]. split; [exact ART2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact FR2|]. split; [exact ES2|]. split; [exact CLE2|].
    split; [| split].
    + intros b j Hj. destruct (Z_lt_le_dec j (15 - Z.of_nat k)) as [LT|GE]; [| exact (ZER2 b j ltac:(lia))].
      rewrite (OLD2 b j ltac:(lia)). assert (Ej : Z.to_nat j = Z.to_nat i) by lia. unfold selw. rewrite Ej. destruct b; apply nth_error_upd_eq; lia.
    + intros b j Hj. rewrite (OLD2 b j ltac:(lia)). unfold selw. destruct b; apply nth_error_upd_neq; lia.
    + intros x Hx HnE. rewrite (PV2 x ltac:(rewrite FRS1; exact Hx) HnE). apply PV1; [| exact HnE].
      apply (aclient_mono _ _ _ _ _ _ _ Hx); [| auto | lia]. rewrite LV2. intros e He. exact (clr_rm_sub _ _ _ He).
Qed.


Definition CLR_W (E : Z) : list (Z * Z) := [(E, E + 904)].

(* [comment removed for export] *)
Definition err_clear_error_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (od e : word) (k MK SA NODES E LV : Z) (pad tw ne : word) (top bot : Z) (fl mk buf fs ls fn : list word)
    (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xbd66f0 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 272 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ERR_clear_error (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) CLR_SITES CLR_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  err_env m od e k MK SA NODES E LV pad tw ne -> err_blocks (rt_live RT Σ) MK SA NODES E -> es_rep m E top bot fl mk buf fs ls fn ->
  (forall b j w, 0 <= j < 16 -> selw fs fn b j = Some w -> slot_free_ok (rt_live RT Σ) (ERRBAD MK SA NODES E) w) ->
  (forall b1 j1 w1 b2 j2 w2, 0 <= j1 < 16 -> 0 <= j2 < 16 -> (b1, j1) <> (b2, j2) -> selw fs fn b1 j1 = Some w1 -> selw fs fn b2 j2 = Some w2 ->
      bv_unsigned w1 <> 0 -> bv_unsigned w1 <> bv_unsigned w2) ->
  cl_env m lb canary ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ERR_clear_error m)))
    (fun c => exists (Σ' : rts RT) (v : word) (fl' mk' buf' ls' : list word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) (CLR_W E) m m'
           /\ err_env m' od e k MK SA NODES E LV pad tw ne /\ es_rep m' E 0 0 fl' mk' buf' (repeat (Z_to_bv 64 0) 16) ls' (repeat (Z_to_bv 64 0) 16) /\ cl_env m' lb canary) c
       /\ rt_live RT Σ' = clr_rm (combine fs fn) (rt_live RT Σ) /\ err_blocks (rt_live RT Σ') MK SA NODES E
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem err_clear_error_cps : err_clear_error_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer od e k MK SA NODES E LV pad tw ne top bot fl mk buf fs ls fn
    lb canary FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hcr ENV BLK ES SOK DIS CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 272 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -48).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 48) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof BLK as (INM & INS & INN & INE & MKAL & SAAL & NAL & EAL).
  pose proof (af_live_range RT AF Σ m MK 72 ART0 INM) as (_ & R1 & R1c). pose proof (af_live_range RT AF Σ m SA 32 ART0 INS) as (_ & R2 & R2c).
  pose proof (af_live_range RT AF Σ m NODES 128 ART0 INN) as (_ & R3 & R3c). pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as (R4a & R4 & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 ART0 INE ltac:(lia)) as EHI. assert (ELO : E + 904 <= lo) by (clear - R4 LOW; lia).
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INM INE ltac:(intros X; injection X; lia)) as D1.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INS INE ltac:(intros X; injection X; lia)) as D2.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INN INE ltac:(intros X; injection X; lia)) as D3.
  (* [comment removed for export] *)
  assert (ENVR : forall LIVE a n x, In (MK, 72) LIVE -> In (SA, 32) LIVE -> In (NODES, 128) LIVE ->
               (0xbd1a00 <= a /\ a + n <= 0xbd2048) \/ (0xbf7aa0 <= a /\ a + n <= 0xbf7e98) \/ (ERRNO_A <= a /\ a + n <= ERRNO_A + 4)
               \/ (MK <= a /\ a + n <= MK + 72) \/ (SA <= a /\ a + n <= SA + 32) \/ (NODES <= a /\ a + n <= NODES + 128) -> a <= x < a + n ->
               aclient LIVE (rt_frames RT Σ) usp x /\ ~ (E <= x < E + 904) /\ x < usp - 48).
  { intros LIVE a' n x IM IS IN H Hx. unfold ERRNO_A, STACK_WIN, RT_STACK, SEGTOP_A in *.
    destruct H as [H|H]. { split; [right; left; apply client_static_intro; right; left; clear - H Hx; lia | clear - H Hx EHI NUM LOW HSTK; lia]. }
    destruct H as [H|H]. { split; [right; left; apply client_static_intro; do 6 right; clear - H Hx; lia | clear - H Hx EHI NUM LOW HSTK; lia]. }
    destruct H as [H|H]. { split; [right; left; apply client_static_intro; right; left; clear - H Hx; lia | clear - H Hx EHI NUM LOW HSTK; lia]. }
    destruct H as [H|H]. { split; [apply (acl_live _ _ _ MK 72); [exact IM | clear - H Hx; lia] | clear - H Hx D1 R1 NUM LOW HSTK; lia]. }
    destruct H as [H|H]. { split; [apply (acl_live _ _ _ SA 32); [exact IS | clear - H Hx; lia] | clear - H Hx D2 R2 NUM LOW HSTK; lia]. }
    split; [apply (acl_live _ _ _ NODES 128); [exact IN | clear - H Hx; lia] | clear - H Hx D3 R3 NUM LOW HSTK; lia]. }
  clear D1 D2 D3 R1c R2c R3c.
  (* [comment removed for export] *)
  pose proof (ecl_w0 ra sp gp (Z_to_bv 64 0xbd66f0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST HLOS HLO1 SPH UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (A01 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 48 _ ART0 ltac:(lia) ltac:(lia) Hx); lia. }
  pose proof ENV as (ICS0 & ERC0 & CH0).
  assert (ICS1 : icstat m1 od).
  { apply (icstat_agree m m1 od ICS0); [| exact WM1]. intros a' n H1 H2 x Hx. cbv beta in Hx. apply A01. exact (proj1 (ENVR _ a' n _ INM INS INN ltac:(left; split; [exact H1 | lia]) Hx)). }
  assert (CH1 : errchain m1 k MK SA NODES E LV pad tw ne).
  { apply (errchain_agree m m1 _ _ _ _ _ _ _ _ _ CH0); [| exact WM1]. intros a' n H x Hx. cbv beta in Hx. apply A01.
    pose proof CH0 as (_ & _ & HK & _). unfold TSD_MAIN_A in H. refine (proj1 (ENVR _ a' n _ INM INS INN _ Hx)). clear - H HK. lia. }
  (* [comment removed for export] *)
  apply (C_GSI0 Σ PMc (Z_to_bv 64 SITE_ecl_egsi) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xbd66f0) t0 t1 t2 sp s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo od k MK SA NODES E LV pad tw ne FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. unfold usp1. lia. }
  { exact Hfr. } { exact Hcr. } { exact ICS1. } { exact CH1. }
  { exact INM. } { exact INS. } { exact INN. } { exact INE. } { exact MKAL. } { exact SAAL. } { exact NAL. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σg & Hc2 & LVg & FRSg & SPg & CRg & CGg).
  destruct (ASTA_unpack RT Σg _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ICS2 & CH2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ecl_egsi) in Hc2' by (unfold SITE_ecl_egsi; lia).
  assert (A02 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m2 x = m x).
  { intros x Hx. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia])). exact (A01 x Hx). }
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2) by (intros a' n H1 H2 x Hx; cbv beta in Hx; apply PRES2; left; lia).
  cl_keep FR1 AG2 WM2 FR2.
  assert (ES2 : es_rep m2 E top bot fl mk buf fs ls fn).
  { apply (es_rep_agree m m2); [exact ES | | exact (wmono_trans bsegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx. apply A02. apply (acl_live _ _ _ E 904); [exact INE | lia]. }
  assert (CLE2 : cl_env m2 lb canary).
  { apply (cl_env_agree m m2 _ _ CLE). intros x Hx. apply A02. right; left; exact (cl_cell_static _ Hx). }
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2) by (intros x Hx; cbv beta in Hx; apply A02; apply acl_stack; exact Hx).
  (* [comment removed for export] *)
  destruct (af_client_consts RT AF Σg m2 ART2) as (_ & _ & _ & _ & UT2).
  pose proof (ecl_w1 (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xbd66f0) u0 u1 u2 sp b1 b2 b3 b4 b5 b6 b7 s1 s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 E
                EHI ltac:(clear - ELO HLO1 SPH; lia) UT2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σg _ _ c3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  pose proof (clr_loop 15 ltac:(lia)) as LOOP. change (15 - Z.of_nat 15) with 0 in LOOP.
  rewrite <- CGg in CTX, CGH. rewrite <- LVg in BLK, SOK.
  apply (LOOP Σg PMc sp gp s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ecl_egsi) u0 u1 u2 (Z_to_bv 64 E) b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 lo outer ra s0 s1 s2 s3 s4
           MK SA NODES E top bot fl mk buf fs ls fn lb canary FDO MST ART2 MI2).
  { fold usp in SPA. unfold call_ok. fold usp usp1. rewrite EU1, SPg. split; [exact ST2|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 3). lia. }
  { fold usp. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite SPg. fold usp. clear - NUM. lia. } { exact SPT. }
  { exact CTX. } { exact (uw_chain_agree outer m m2 sp s0 UWC AG02). } { exact CGH. }
  { exact FR2. } { exact BLK. } { exact ES2. } { lia. } { exact SOK. } { exact DIS. } { exact CLE2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ3 & fl3 & mk3 & buf3 & fs3 & ls3 & fn3 & Hc4 & LV3 & BLK3 & FRS3 & SP3 & CR3 & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c4 Hc4) as (ms4 & (ra' & v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & s2x & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & -> &
                                               ART3 & MI3 & ST3 & FR3 & ES3 & CLE3 & ZER3 & OLD3 & PV3) & Hc4'). clear Hc4.
  pose proof BLK3 as (INM3 & INS3 & INN3 & INE3 & _).
  destruct (af_client_consts RT AF Σ3 m3 ART3) as (_ & _ & _ & _ & UT3).
  pose proof (proj2 (af_acc_live RT AF Σ3 m3 E 904 ART3 INE3)) as ACCE3.
  (* [comment removed for export] *)
  pose proof ES3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB3 & _ & _).
  pose proof (ecl_wz sp gp (Z_to_bv 64 0xbd66f0) v0 v1 v2 d0 d1 d2 d3 d4 d5 d6 d7 s2x s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 ra' ra s0 s1 s2 s3 s4 F3 fc3 m3 lo E (Z_to_bv 64 top) (Z_to_bv 64 bot)
                EHI ELO EAL ST3 HLOS ltac:(fold usp; clear - HLO1; lia) SPH UT3 ACCE3 FR3 TB3 MI3) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ3 _ _ c5 Hc5) as (ms5 & (g1 & g2 & m4 & -> & MU4 & WM4 & MI4 & TB4 & ST4) & Hc5'). clear Hc5.
  fold usp in ST4.
  pose proof (es_rep_set_tb m3 m4 E top bot fl3 mk3 buf3 fs3 ls3 fn3 ES3 MU4 WM4 TB4) as ES4.
  assert (ART4 : ART RT Σ3 m4).
  { apply (af_frame RT AF Σ3 m3 m4 usp1 ART3 ltac:(rewrite SP3, SPg; unfold usp1; clear - NUM; lia)); [| exact WM4].
    intros x Hx. apply MU4. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE3 | clear - Hin; lia]. }
  assert (A04 : forall x : word, aclient (rt_live RT Σ3) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m4 x = m x).
  { intros x Hx HnE. rewrite (MU4 x ltac:(cbn [outside]; clear - HnE; lia)). rewrite (PV3 x ltac:(rewrite FRSg; exact Hx) HnE).
    apply A02. apply (aclient_mono _ _ _ _ _ _ _ Hx); [| auto | lia]. rewrite LV3. intros e0 He. rewrite <- LVg. exact (clr_rm_sub _ _ _ He). }
  pose proof ES3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L7 & _ & _ & _ & L9 & _).
  assert (EFS : fs3 = repeat (Z_to_bv 64 0) 16).
  { apply all_zero_repeat; [exact L7|]. intros j w Hj.
    destruct (Nat.lt_ge_cases j 16) as [Hj16|Hj16]; [| rewrite (proj2 (nth_error_None fs3 j)) in Hj by lia; discriminate].
    pose proof (ZER3 false (Z.of_nat j) ltac:(lia)) as Z0. unfold selw in Z0. change (if false then fn3 else fs3) with fs3 in Z0. rewrite Nat2Z.id in Z0. rewrite Z0 in Hj. congruence. }
  assert (EFN : fn3 = repeat (Z_to_bv 64 0) 16).
  { apply all_zero_repeat; [exact L9|]. intros j w Hj.
    destruct (Nat.lt_ge_cases j 16) as [Hj16|Hj16]; [| rewrite (proj2 (nth_error_None fn3 j)) in Hj by lia; discriminate].
    pose proof (ZER3 true (Z.of_nat j) ltac:(lia)) as Z0. unfold selw in Z0. change (if true then fn3 else fs3) with fn3 in Z0. rewrite Nat2Z.id in Z0. rewrite Z0 in Hj. congruence. }
  rewrite EFS, EFN in ES4.
  apply Hk. exists Σ3, (Z_to_bv 64 (E + 896)), fl3, mk3, buf3, ls3.
  split; [| split; [rewrite LV3, LVg; reflexivity | split; [exact BLK3 | split; [rewrite FRS3; exact FRSg | split; [rewrite SP3; exact SPg | split; [rewrite CR3; exact CRg | rewrite CG3; exact CGg]]]]]].
  eapply ASTA_conseq; [exact Hc5'|]. intros ms <-. exists m4.
  split; [exists v0, v1, v2, g1, g2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F3, fc3; reflexivity|].
  split; [exact (conj ART4 (conj MI4 ST4))|].
  split. { intros x Hx Ho. unfold CLR_W in Ho. cbn [outside] in Ho. exact (A04 x Hx ltac:(clear - Ho; lia)). }
  assert (AGF : forall a' n, (0xbd1a00 <= a' /\ a' + n <= 0xbd2048) \/ (0xbf7aa0 <= a' /\ a' + n <= 0xbf7e98) \/ (ERRNO_A <= a' /\ a' + n <= ERRNO_A + 4)
               \/ (MK <= a' /\ a' + n <= MK + 72) \/ (SA <= a' /\ a' + n <= SA + 32) \/ (NODES <= a' /\ a' + n <= NODES + 128) -> agree_on (fun x => a' <= x < a' + n) m m4).
  { intros a' n H x Hx. cbv beta in Hx. destruct (ENVR (rt_live RT Σ3) a' n _ INM3 INS3 INN3 H Hx) as (Q1 & Q2 & _). exact (A04 x Q1 Q2). }
  split.
  { split; [| split].
    - apply (icstat_agree_nw m m4 od ICS0). intros a' n H1 H2. apply AGF. left. clear - H1 H2. lia.
    - apply (rw_cells_agree_nw bsegs m m4 _ _ ERC0). apply AGF. do 2 right; left. cbn [cells_size csize Nat.add]. lia.
    - apply (errchain_agree_nw m m4 _ _ _ _ _ _ _ _ _ CH0). intros a' n H. apply AGF. pose proof CH0 as (_ & _ & HK & _). unfold TSD_MAIN_A in H. clear - H HK. lia. }
  split; [exact ES4|].
  apply (cl_env_seg _ m3 m4 lb canary CLE3 MU4). cl_fp_lia.
Qed.
End CClr.
