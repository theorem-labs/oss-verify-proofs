(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Lemma rt_wfx_of_wf : forall Σ, rt_wf Σ -> rt_wfx Σ /\ rt_count Σ.
Proof.
  intros Σ (H1 & H2 & H3 & H4 & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) & H6 & H7 & H8 & H9 & H10 & H11 & HC).
  split; [|exact HC].
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 H11)))))))))).
  unfold quar_wfx. split; [unfold QMAX_L in *; lia|]. split; [lia|].
  exact (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 Q8))))).
Qed.

Definition rec_ret_st (usp T : Z) (gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a0 a1 a2 a3 a4 a5 a6 a7
          s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x63308) fc None m (seg_rom bsegs).

Lemma ret_tailP : forall (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
    t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 wc ws : word) (F : bvmap 5 word) (fc : bv 32) (m5 : mem) (lo : Z),
  geo_ok Σ2 -> ARTc Σ2 m5 -> rt_wfx Σ2 -> rt_count Σ2 -> RT_state.qbytes (ql Σ2) <= 0x100000 ->
  mem_inv bsegs m5 -> stk bsegs m5 lo (bv_unsigned sp + -2208) -> l_ACEIL (lay Σ2) <= lo -> lo + 0x10000 <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP ->
  icpt_frame m5 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5 ->
  qput_frame m5 (bv_unsigned sp + -2208) wc ws (Z_to_bv 64 0x86460) w0 w1 w2 w3 w4 w5 s6 ->
  evt bsegs (fin_post Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m5)
    (rec_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5).
Proof.
  intros Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 wc ws F fc m5 lo
    HG ART5 HWX HC HBY MI5 ST5 HLO HLO2 Husp ICF FR5.
  set (usp := bv_unsigned sp) in *.
  pose proof (fk_aceil Σ2 HG) as (X1 & X2).
  assert (RSP2 : 0 <= usp + -2128 < 2 ^ 64) by (clear - HLO HLO2 Husp X1; unfold USTACK_TOP, SHB in *; lia).
  pose proof ART5 as (_ & _ & _ & _ & _ & QR & _). destruct QR as (QT & _).
  pose proof QT as QT'. apply (proj1 (qcache_rep_iff _ _ _)) in QT'. destruct QT' as (QH & _).
  unfold rec_ret_st.
  replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80))
    by (rewrite (unsigned_lit (usp + -2128)) by exact RSP2; f_equal; lia).
  replace (usp + -2208) with (usp + -2128 - 80) in ST5, FR5 by lia.
  pose proof (qbytes_nonneg _ _ (qwf_ql_x Σ2 HWX)) as QB0.
  eapply evt_cut.
  { apply (qput_P_ret_spec (Z_to_bv 64 0x86460) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s2' s3' s4' s5' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11
             t3 t4 t5 t6 ra0 w0 w1 w2 w3 w4 w5 s6 wc ws F fc m5 (l_T (lay Σ2) + 80) (R_quar_defs.qbytes (ql Σ2)) lo
             (Z_to_bv 64 (Z.of_nat (length (ql Σ2)))) (Z_to_bv 64 (qfirst (ql Σ2))) (Z_to_bv 64 (qlast (ql Σ2))));
      try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP2.
    all: try exact ST5. all: try exact FR5. all: try (clear - HLO2; lia). all: try (clear - X1 HLO; unfold SHB in *; lia).
    rewrite qbytes_eq. clear - QB0 HBY. rewrite qbytes_eq in QB0. lia. }
  intros ms6 P6. destruct P6 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6).
  rewrite (unsigned_lit (usp + -2128)) in MU6, ST6 by exact RSP2. rewrite (ret_pc_even 0x86460) by (first [reflexivity | lia]).
  destruct ICF as (FRs & (jp & FRp) & FRt & (wsb & TB & HTB) & (w & FRb)).
  assert (DSF : forall a k, usp - 2128 <= a -> disjoint_from [(usp + -2128 - 80, usp + -2128)] a k).
  { intros a k H1. cbn [disjoint_from]. split; [lia | exact I]. }
  pose proof (rw_cells_transport bsegs _ m5 m6 _ _ FRs MU6 WM6 ltac:(apply DSF; lia)) as FRs6.
  pose proof (rw_cells_transport bsegs _ m5 m6 _ _ FRp MU6 WM6 ltac:(apply DSF; lia)) as FRp6.
  pose proof (rw_cells_transport bsegs _ m5 m6 _ _ FRt MU6 WM6 ltac:(apply DSF; lia)) as FRt6.
  pose proof (rw_cells_transport bsegs _ m5 m6 _ _ FRb MU6 WM6 ltac:(apply DSF; lia)) as FRb6.
  pose proof (u64arr_transport bsegs _ m5 m6 _ _ TB MU6 WM6 ltac:(apply DSF; lia)) as TB6.
  clear FRs FRp FRt FRb TB.
  replace (Z_to_bv 64 (usp + -2128)) with (Z_to_bv 64 (bv_unsigned sp + -2128)) by reflexivity.
  eapply evt_mono.
  { apply (free_B_spec ra sp gp (Z_to_bv 64 tpA) y0 y1 y2 w0 w1 y3 y4 y5 y6 y7 y8 y9 y10 w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 y11 y12 y13 y14
             (Z_to_bv 64 0x86460) s0 s1 s2 s3 s4 s5 F fc m6 lo wsb w jp); try assumption.
    all: try (clear - HLO2; lia). all: try (clear - X1 HLO; unfold SHB in *; lia). }
  intros ms P7. destruct P7 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m7 & -> & MU7 & WM7 & MI7 & ST7).
  pose proof (wmono_trans bsegs _ _ _ WM6 WM7) as WM57.
  lazymatch type of MU7 with munch ?W7 _ _ => lazymatch type of MU6 with munch ?W6 _ _ =>
    pose proof (munch_trans [(usp - 2208, usp)] m5 m6 m7 (munch_weaken W6 [(usp - 2208, usp)] m5 m6 ltac:(clear - HLO2; solve_sub_fp) MU6)
                  (munch_weaken W7 [(usp - 2208, usp)] m6 m7 ltac:(clear - HLO2; solve_sub_fp) MU7)) as MU57 end end.
  unfold fin_post. exists z3, z0, z1, z2, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m7. split; [reflexivity|].
  split; [|split; [exact MI7 | split; [exact WM57 | split; [exact ST7 | exact MU57]]]].
  apply c_ART; [exact (rt_wf_of_x Σ2 HWX HC ltac:(clear - HBY; unfold QMAX_L; lia))|].
  apply (ARTc_stack Σ2 (usp - 2208) usp HG ltac:(clear - HLO HLO2; lia) m5 m7 ART5 MU57 WM57).
  - destruct HWX as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB.
  - destruct HWX as (_ & _ & _ & _ & _ & _ & _ & DOK & _). exact DOK.
Qed.

End GWIN.
