(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_ut RT_iface_pem Fz_kit Fz_chk Fz_M_malloc Fz_env Fz_mkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition SITE_cr_realloc : Z := 0x1fc3b8.

(* [comment removed for export] *)
Definition crealloc_s0_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a2' a4' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_cr_realloc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a3
                 (Z_to_bv 64 p) (Z_to_bv 64 n) a2' a3 a4' a5 a6 a7 a2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_realloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma crealloc_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p n lo : Z),
  0 < p < 2^63 -> 0 < n < 2^63 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> SEGTOP_A <= lo -> bv_unsigned sp <= 2^47 ->
  ro_cells asegs m CL_REALLOC_IMPL [C8 (Z_to_bv 64 e_CRYPTO_realloc)] -> img_untouched m -> mem_inv asegs m ->
  evt asegs (crealloc_s0_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a5 a6 a7 t3 t4 t5 t6 F fc p n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_realloc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros Hp Hn ST HLO HIMG SPH RIMP UT MI. unfold e_CRYPTO_realloc, CL_REALLOC_IMPL, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(bv_unsigned sp - 48, bv_unsigned sp)]) by ut_fp_lia.
  carve_frame 40%nat ST. carve_frame 8%nat ST.
  do 7 zstep. do 3 zstep. do 4 zstep. zstep. ifT.
  zstep. ifF. zstep. ifF. do 2 zstep.
  unfold crealloc_s0_post, SITE_cr_realloc, e_realloc. apply evt_done.
  lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -48) [CB 8 ?j] |- _ => do 2 eexists; exists j; eexists end.
  split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [| eassumption].
  lazymatch goal with H1 : rw_cells asegs ?mm (bv_unsigned sp + -48) [CB 8 ?j], H2 : rw_cells asegs ?mm (bv_unsigned sp + -40) ?cs |- _ =>
    pose proof (rw_cells_app mm (bv_unsigned sp + -48) [CB 8 j] cs) as X; cbn [cells_size csize Nat.add app] in X;
    replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in X by lia; exact (proj2 X (conj H1 H2)) end.
Qed.

(* [comment removed for export] *)
Definition crealloc_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (q lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma crealloc_s1_walk : forall ra0 ra sp gp tp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (q lo : Z) (j : list byte),
  0 < q < 2^63 ->
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp + -48 -> SEGTOP_A <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv asegs m ->
  evt asegs (crealloc_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc q lo m)
    (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_cr_realloc) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros Hq ST HLO HIMG SPH FR MI. unfold SITE_cr_realloc, SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. ifF. zstep.
  do 6 zstep.
  release_frame FR ST SP.
  zstep.
  unfold crealloc_s1_post. apply evt_done. eexists. split; [subst SP; rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
  rewrite (unsigned_lit SP) by lia. replace (SP - 48) with (SP + -48) by lia. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Section CRealloc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RLC : realloc_contract RT.

(* [comment removed for export] *)
Definition crypto_realloc_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n0 n lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 ->
  In (p, n0) (rt_live RT Σ) -> 1 <= n <= 64512 -> 1 <= n0 <= 64512 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 48 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_realloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_cr_realloc, e_CRYPTO_realloc)] [(SITE_cr_realloc, e_realloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_realloc m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) m m'
           /\ cl_env m' lb canary /\ wr_at asegs m' q n /\ acc asegs m' q n
           /\ (forall bs, bytes_at asegs m p bs -> Z.of_nat (length bs) = Z.min n0 n -> bytes_at asegs m' q bs)) c
       /\ rt_live RT Σ' = (q, n) :: live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_realloc_cps : crypto_realloc_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n0 n lo outer lb canary
    FDO MST -> -> -> Hin Hn Hn0 ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m p n0 ART0 Hin) as (Pp0 & PLO & PIMG).
  assert (Pp63 : 0 < p < 2^63) by (unfold USTACK_TOP, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  cl_eu usp (-48) EU1.
  (* [comment removed for export] *)
  pose proof (crealloc_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
                Pp63 ltac:(lia) ST ltac:(fold usp; unfold RT_STACK in *; lia) HLOI ltac:(fold usp; unfold USTACK_TOP in *; lia)
                (cl_env_rimp m lb canary ENV) UT MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a2' & a4' & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  (* [comment removed for export] *)
  apply (RLC Σ PMc (Z_to_bv 64 SITE_cr_realloc) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp a3 (Z_to_bv 64 p) (Z_to_bv 64 n) a2' a3 a4' a5 a6 a7
           a2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p n0 n lo FDO MST Hin Hn Hn0 eq_refl eq_refl eq_refl Hlen Hcr ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { apply (cl_unwind_call (rt_cg RT Σ) e_CRYPTO_realloc e_realloc SITE_cr_realloc m m1 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTX
             (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) ltac:(unfold SITE_cr_realloc; lia) UWC AG1).
    - fold usp. replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [CB 8 j; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia).
      exact (rw_cells_skip m1 (usp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1).
    - rewrite EU1. fold usp. lia.
    - exact SPT. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ' & q & Hc2 & LV & FRS & SP0 & CR & Q0 & Q16 & QU & CG).
  destruct (ASTA_unpack RT Σ' _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & WR2 & ACC2 & CPY2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_cr_realloc) in Hc2' by (unfold SITE_cr_realloc; lia).
  (* [comment removed for export] *)
  assert (FR2 : rw_cells asegs m2 (usp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  pose proof (crealloc_s1_walk (Z_to_bv 64 SITE_cr_realloc) ra sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp a3 b1 b2 b3 b4 b5 b6 b7 a2 (Z_to_bv 64 n)
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 q lo j ltac:(unfold USTACK_TOP in *; lia) ST2
                ltac:(fold usp; unfold RT_STACK in *; lia) HLOI ltac:(fold usp; unfold USTACK_TOP in *; lia) FR2 MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3. apply Hk. exists Σ', q.
  split; [| exact (conj LV (conj FRS (conj SP0 (conj CR (conj Q0 (conj Q16 (conj QU CG)))))))].
  apply (ASTA_conseq RT Σ' PMc _ _ c3 Hc3). intros ms3 (m3 & -> & MU3 & WM3 & MI3 & ST3). exists m3. fold usp in MU3, ST3.
  split; [exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F2, fc2; reflexivity|].
  pose proof (cl_seg_ART RT AF Σ' m2 m3 usp 48 [] ART2 ltac:(rewrite SP0; lia) ltac:(lia) MU3 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM3) as ART3.
  split; [exact (conj ART3 (conj MI3 ST3))|].
  split.
  { intros a Ha.
    assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (live_remove_sub _ _ _ He) | auto | lia]).
    pose proof (cl_split RT AF Σ m usp 48 _ ART0 ltac:(lia) ltac:(lia) Ha0) as N4.
    rewrite (MU3 a ltac:(cbn [app outside]; split; [lia | exact I])).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | lia])).
    exact (PR1 a Ha0 I). }
  split; [apply (cl_env_seg _ m2 m3 lb canary (cl_env_pres _ _ _ m1 m2 lb canary ENV1 PRES2) MU3); cl_fp_lia|].
  assert (INQ : In (q, n) (rt_live RT Σ')) by (rewrite LV; left; reflexivity).
  pose proof (af_acc_live RT AF Σ' m3 q n ART3 INQ) as (WR3 & ACC3).
  split; [exact WR3|]. split; [exact ACC3|].
  intros bs Hbs Hbl.
  assert (Hb1 : bytes_at asegs m1 p bs).
  { apply (bytes_at_agree asegs m m1 p bs Hbs). intros a Ha. cbv beta in Ha. apply PR1; [| exact I].
    right; right; left. exists p, n0. split; [exact Hin | lia]. }
  pose proof (af_live_range RT AF Σ' m2 q n ART2 INQ) as (_ & QLO & _). rewrite SP0 in QLO.
  apply (bytes_at_transport asegs _ m2 m3 q bs (CPY2 bs Hb1 Hbl) MU3).
  cbn [app disjoint_from]. split; [left; lia | exact I].
Qed.

End CRealloc.
