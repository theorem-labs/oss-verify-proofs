(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_libiface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_master1 Fz_T_sk Fz_T_mtl Fz_T_its Fz_I1_defs Fz_I1_loadw Fz_I1_errload Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0 Fz_W5_rep Fz_W5_agr Fz_W2_exdc Fz_W5_env Fz_I3_glx0 Fz_G_OSSL_ERR_STATE_new Fz_I3_icfast Fz_I3_egsiw Fz_I3_egsi Fz_I3_ibasew Fz_I3_ibase Fz_I3_loadstrw Fz_I3_loadstr Fz_I3_fullw Fz_I3_full Fz_I3_eclw Fz_I3_eclear Fz_I3_gdcw Fz_I3_gdc Fz_I3_fxiw Fz_I3_fxi Fz_lib0 Fz_libA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).

Definition e_FI : Z := 0x1f307c.                (* [comment removed for export] *)
Definition FI_RET1 : Z := 0x1f3090. Definition FI_RET2 : Z := 0x1f3094. Definition FI_RET3 : Z := 0x1f30a0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fi_w0_post (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j8 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 FI_RET1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_init_crypto) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [CB 8 j8; C8 rae] /\ stk asegs m' lo (bv_unsigned sp + -16).

Lemma fi_w0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> img_untouched m -> mem_inv asegs m ->
  evt asegs (fi_w0_post sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae F fc lo m)
    (MS (mkR rae sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_fuzz_init) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLOS HLO SPH UT MI. unfold e_fuzz_init.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 16, SP)]) by ut_fp_lia.
  ths.
  carve_frame 16%nat ST.
  do 2 ths.
  lazymatch goal with FRH : rw_cells asegs ?mm (SP + -16) (CB 8 ?jj :: ?rest) |- _ => set (j8 := jj) in FRH end.
  do 3 ths.
  subst SP. rewrite ?Z_to_bv_bv_unsigned. unfold fi_w0_post, FI_RET1, e_init_crypto. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

Lemma fi_w1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem),
  img_untouched m ->
  evt asegs (eq (MS (mkR (Z_to_bv 64 FI_RET2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_eclear) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 FI_RET1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FI_RET1) fc None m (seg_rom asegs)).
Proof. intros until m. intros UT. unfold FI_RET1, FI_RET2, e_eclear. ths. apply evt_done. reflexivity. Qed.

Lemma fi_w2 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem),
  img_untouched m ->
  evt asegs (eq (MS (mkR (Z_to_bv 64 FI_RET3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 e_fxi) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 FI_RET2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FI_RET2) fc None m (seg_rom asegs)).
Proof. intros until m. intros UT. unfold FI_RET2, FI_RET3, e_fxi. do 3 ths. apply evt_done. reflexivity. Qed.

Definition fi_w3_post (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR rae sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rae) fc None m (seg_rom asegs)
            /\ stk asegs m lo (bv_unsigned sp).

Lemma fi_w3 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (ra rae : word) (j8 : list byte)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -16) [CB 8 j8; C8 rae] -> mem_inv asegs m ->
  evt asegs (fi_w3_post sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae F fc lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FI_RET3) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLOS HLO SPH UT FR MI. unfold FI_RET3.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  ths. ths. release_frame FR ST SP. ths. ths.
  subst SP. rewrite ?Z_to_bv_bv_unsigned. unfold fi_w3_post. apply evt_done. split; [reflexivity | assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lh_repE_pos : forall GOBJ m L lh B g bks, lh_repE GOBJ m L lh B g bks -> forall p n, In (p, n) L -> 0 < n.
Proof.
  intros GOBJ m L lh B g bks (REP & PERM & _) p n Hin.
  pose proof (lh_geo_bounds g (proj1 REP)) as (GB & _).
  pose proof (Permutation_in _ PERM Hin) as H. cbn [In] in H. destruct H as [H|[H|H]]; [injection H; lia | injection H; lia |].
  apply in_map_iff in H as (x & E & _). injection E. lia.
Qed.

Lemma rw_u32 : forall (m : mem) A cs ws, rw_cells asegs m A cs -> cells_bytes cs = u32s ws -> cells_size cs = (4 * length ws)%nat -> u32arr asegs m A ws.
Proof. intros m A cs ws [[WF B] W] E1 E2. split; [rewrite <- E1; exact B | rewrite E2 in W; rewrite Nat2Z.inj_mul in W; exact W]. Qed.
Lemma rw_u64 : forall (m : mem) A cs ws, rw_cells asegs m A cs -> cells_bytes cs = u64s ws -> cells_size cs = (8 * length ws)%nat -> u64arr asegs m A ws.
Proof. intros m A cs ws [[WF B] W] E1 E2. split; [rewrite <- E1; exact B | rewrite E2 in W; rewrite Nat2Z.inj_mul in W; exact W]. Qed.
Lemma rw_u8 : forall (m : mem) A cs bs, rw_cells asegs m A cs -> cells_bytes cs = bs -> cells_size cs = length bs -> u8arr asegs m A bs.
Proof. intros m A cs bs [[WF B] W] E1 E2. split; [rewrite <- E1; exact B | rewrite E2 in W; exact W]. Qed.

Lemma es_at_rest_of_arrs : forall (m : mem) E, ecl_arrs m E 16 -> es_at_rest m E.
Proof.
  intros m E (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). cbn [Nat.sub repeat] in A0, A1, A2, A3, A4, A5, A6, A7, A8. rewrite app_nil_r in A0, A1, A2, A3, A4, A5, A6, A7, A8.
  exists (repeat (Z_to_bv 64 0) 16), (repeat (Z_to_bv 64 0) 16), (repeat (Z_to_bv 64 0) 16), (repeat ECL_LNW 16).
  split; [exact (rw_u32 m _ _ (repeat (Z_to_bv 64 0) 16) A0 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u32 m _ _ (repeat (Z_to_bv 64 0) 16) A1 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u64 m _ _ (repeat (Z_to_bv 64 0) 16) A2 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u8 m _ _ (repeat (Z_to_bv 8 0) 128) A3 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (rw_u8 m _ _ (repeat (Z_to_bv 8 0) 128) A4 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (rw_u8 m _ _ (repeat (Z_to_bv 8 0) 64) A5 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (rw_u64 m _ _ (repeat (Z_to_bv 64 0) 16) A6 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u32 m _ _ (repeat ECL_LNW 16) A7 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (rw_u64 m _ _ (repeat (Z_to_bv 64 0) 16) A8 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact A9|]. lia.
Qed.


(* [comment removed for export] *)
Lemma outside_cover : forall (LW W : list (Z * Z)) (x : Z), outside LW x ->
  (forall lo hi, In (lo, hi) W -> (exists lo' hi', In (lo', hi') LW /\ lo' <= lo /\ hi <= hi') \/ ~ (lo <= x < hi)) -> outside W x.
Proof.
  intros LW W x Ho HW. induction W as [|[wl wh] W IH]; [exact I|]. cbn [outside]. split.
  - destruct (HW wl wh (or_introl eq_refl)) as [(lo' & hi' & Hin & H1 & H2)|H]; [| exact H]. intros Hx.
    clear - Ho Hin Hx H1 H2. induction LW as [|[u v] L IHL]; [destruct Hin|]. cbn [outside] in Ho. destruct Ho as [HO1 HO2].
    destruct Hin as [EQ|Hin]; [injection EQ as <- <-; lia | exact (IHL HO2 Hin)].
  - apply IH. intros lo1 hi1 Hin1. exact (HW lo1 hi1 (or_intror Hin1)).
Qed.

(* [comment removed for export] *)
Section PermApart.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma perm_live_apartF : forall Σ (m : mem) x rest y, ART RT Σ m -> Permutation (rt_live RT Σ) (x :: rest) -> In y rest ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using AF.
  intros Σ m x rest y ART0 P Hy.
  pose proof (Permutation_in x (Permutation_sym P) (or_introl eq_refl)) as INx. destruct (in_split _ _ INx) as (A & B & E).
  assert (Hy' : In y (A ++ B)).
  { apply (Permutation_in y (l := rest)); [| exact Hy]. apply (@Permutation_cons_app_inv _ rest A B x). rewrite <- E. apply Permutation_sym. exact P. }
  destruct x as [p1 n1], y as [p2 n2]. exact (af_live_disj RT AF Σ m p1 n1 p2 n2 A B ART0 E Hy').
Qed.
End PermApart.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Finit.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_FULL : init_crypto_full_stmt RT GOBJ.
Hypothesis C_ECL : eclear_first_stmt RT.
Hypothesis C_FXI : fxi_stmt RT.
Variables FZ_SITES FZ_CALLS : list (Z * Z).

(* [comment removed for export] *)
Definition FI_SITES : list (Z * Z) := [(FI_RET1, e_FI); (FI_RET2, e_FI); (FI_RET3, e_FI)] ++ ICF_SITES ++ ECLR_SITES ++ FXI_SITES.
Definition FI_CALLS : list (Z * Z) :=
  [(FI_RET1, e_init_crypto); (FI_RET2, e_eclear); (FI_RET3, e_fxi); (FI_RET3, e_fxi_ex); (RA_INIT, e_fuzz_init); (RA_INIT, e_FI)] ++ ICF_CALLS ++ ECLR_CALLS ++ FXI_CALLS.
Hypothesis HCG : cg_sub FI_SITES FI_CALLS FZ_SITES FZ_CALLS.

Theorem fuzz_init_A : fuzz_init_cps RT LIB0_A LIB_A FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST -> -> FRS0 POS Hlen Hcr FPI CGH0 LIB0 IOSSP ERRNO ART0 MI0 ST LOW HSTK SPT SPA SPTOP.
  intros T c HA Hk. unfold FUZZ_STACK in HSTK.
  pose proof (cg_has_of_sub _ _ _ _ _ CGH0 HCG) as CGH.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - FUZZ_STACK /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ usp <= 2^47) by (unfold FUZZ_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -16). cl_eu usp (-16) EU1. fold usp1 in EU1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  destruct LIB0 as ((MIMP & RIMP & FIMP & MSF & LAT & STP & OD & BONCE & BRET & LSO & LSR & OLC & ILC & IK & BI & DK2 & TVO & TVR & TVG & MKO & MKK & MKI
                     & EONC & ELK & EHC & EFL & DC740 & DC720 & DC760 & DC780 & DC7A0 & DC560 & DC580 & DC588 & DC5F0
                     & X628 & X630 & X638 & X640 & X648 & X650 & X658 & X660 & X668 & X670 & X678 & X680 & X688 & X690 & X698 & X6A0 & X6A8 & X6B0 & X6B8 & SEC)
                    & (nk & j1 & w & sh & oldcb & u & HNK & HJ1 & HJ3 & NK & KL & KW & CASE & K0 & K1 & K2 & K3 & T1 & T2 & T3 & CBC & U150)).
  destruct IOSSP as (g & _ & SSPG). destruct ERRNO as (e0 & ERR0). unfold errno_cell in ERR0. rewrite unsigned_lit in ERR0 by lia.
  assert (CLE : cl_env m (Z_to_bv 8 0) g).
  { split; [| split; [exact LAT | split; [left; reflexivity | exact (ssp_guard_rw m g SSPG)]]].
    unfold CL_RO, G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, e_CRYPTO_malloc, e_CRYPTO_realloc, e_CRYPTO_free, e_wrap_memset.
    repeat apply Forall_cons; [exact (wg_rw_ro _ _ _ MIMP) | exact (wg_rw_ro _ _ _ RIMP) | exact (wg_rw_ro _ _ _ FIMP) | exact (wg_rw_ro _ _ _ MSF) | apply Forall_nil]. }
  (* [comment removed for export] *)
  pose proof (fi_w0 sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 RA_INIT) F fc m lo
                ST ltac:(clear - NUM; lia) ltac:(clear - HSTK; unfold FUZZ_STACK in *; lia) ltac:(clear - NUM; lia) UT MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j8 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 16, usp)]) m m1) by exact MU1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(clear - NUM; unfold FUZZ_STACK in *; lia) ltac:(clear - NUM; lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(clear - NUM; unfold FUZZ_STACK in *; lia) ltac:(clear; lia) MU1') as PR1.
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= 0x10007fff8000 -> rw_cells asegs m1 a cs).
  { intros a cs H R. apply (wg_keep_seg _ m m1 _ _ H MU1 WM1). intros x Hx. cbn [app outside]. clear - Hx R NUM HSTK. unfold FUZZ_STACK in *. lia. }
  pose proof (cl_env_seg _ m m1 _ g CLE MU1 ltac:(first [solve [clear - NUM HSTK; unfold FUZZ_STACK in *; cl_fp_lia] | cl_fp_lia])) as CLE1.
  (* [comment removed for export] *)
  apply (C_FULL Σ PMc (Z_to_bv 64 FI_RET1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 2) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 lo (Z_to_bv 8 0) g nk j1 w e0 sh (Z_to_bv 64 0) oldcb (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
           (Z_to_bv 64 0xffffffff) (Z_to_bv 64 0) (Z_to_bv 8 0) u (Z_to_bv 8 0) FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 1. }
  { rewrite EU1. clear - HSTK. unfold usp1, FUZZ_STACK, RT_STACK in *. lia. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS0. cbn [length]. clear; unfold FRAMES_MAX; lia. }
  { clear - Hlen. unfold CLI_MAX, FUZZ_LIVE in *. lia. }
  { clear - Hcr. unfold INIT_COST in *. lia. }
  { apply Forall_forall. intros [p n] Hin. cbn [snd]. exact (POS p n Hin). }
  { exact CLE1. }
  { exact (STAT1 _ _ STP ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ OD ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ BONCE ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ BRET ltac:(cbn; clear; lia)). }
  { exact (STAT1 _ _ LSO ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ LSR ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ OLC ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ ILC ltac:(cbn; clear; lia)). }
  { exact (STAT1 _ _ (rw_cells_head m _ _ _ DK2) ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ IK ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ BI ltac:(cbn; clear; lia)). }
  { exact (STAT1 _ _ NK ltac:(cbn; clear; lia)). } { clear - HNK HJ3 CASE; lia. } { exact (STAT1 _ _ KL ltac:(cbn; clear; lia)). }
  { exact (wg_rw_ro _ _ _ (STAT1 _ _ KW ltac:(cbn [cells_size csize Nat.add]; clear - HNK HJ3 CASE; lia))). } { exact CASE. } { clear - HJ3; lia. }
  { exact (STAT1 _ _ K0 ltac:(cbn [cells_size csize Nat.add]; clear - HJ1 HJ3; lia)). } { exact (STAT1 _ _ K1 ltac:(cbn [cells_size csize Nat.add]; clear - HJ1 HJ3; lia)). }
  { exact (STAT1 _ _ K2 ltac:(cbn [cells_size csize Nat.add]; clear - HJ1 HJ3; lia)). }
  { exact (STAT1 _ _ ERR0 ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ MKO ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ MKI ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ MKK ltac:(cbn; clear; lia)). }
  { exact (STAT1 _ _ T2 ltac:(cbn [cells_size csize Nat.add]; clear - HJ1 HJ3; lia)). } { exact (STAT1 _ _ U150 ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ CBC ltac:(cbn; clear; lia)). }
  { exact (STAT1 _ _ EONC ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ ELK ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ EHC ltac:(cbn; clear; lia)). } { exact (STAT1 _ _ EFL ltac:(cbn; clear; lia)). }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & p1 & p2 & MK & SA & P & pk & lh & B & L' & g' & bks' & lb' & u' & e' & top' & Hc2 & PERM1 & LL1 & IT1 & FRS1 & SP1 & CR1 & CG1 & B1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & CLE2 & STP2 & OD2 & BONCE2 & BRET2 & LSO2 & LSR2 & OLC2 & ILC2 & P1C & P2C & DK_2 & IK2 & BI2
                       & NK2 & KL2 & KD0 & KD1 & KD2 & ERR2 & MKO2 & MKI2 & MKK2 & TSK2 & U2 & CBC2 & MKC2 & SAC2 & HTOP2 & PC2 & ERS2 & PKC2 & REP2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even FI_RET1) in Hc2' by (unfold FI_RET1; lia).
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  destruct B1 as (P10 & P116 & P1U & P20 & P216 & P2U & MK0 & MK16 & MKU & SA0 & SA16 & SAU & P0 & P16 & PU & PK0 & PK16 & PKU).
  (* [comment removed for export] *)
  assert (HJ0 : 1 <= j1) by exact HJ1.
  assert (K12 : forall a cs, rw_cells asegs m1 a cs -> a + Z.of_nat (cells_size cs) <= 0x10007fff8000 ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> client_static x /\ outside (ICF_W j1) x) -> rw_cells asegs m2 a cs).
  { intros a cs H R HO. apply (rw_cells_agree_nw asegs m1 m2 _ _ H). intros x Hx. destruct (HO _ Hx) as [H1 H2]. apply PRES2; [right; left; exact H1 | exact H2]. }
  Ltac k12 K H := apply (K _ _ H); [cbn [cells_size csize Nat.add]; clear; lia | cbn [cells_size csize Nat.add]; intros x Hx; split;
    [apply client_static_intro; clear - Hx; lia | unfold ICF_W, IB_W, LS_W; cbn [outside app]; unfold G_IC_BASE_ONCE, G_LS_ONCE, G_IC_OPTSDONE, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET in *; clear - Hx; repeat split; lia]].
  assert (DK4_2 : rw_cells asegs m2 (0x5a9f20 + 4) [C4 (Z_to_bv 64 0xffffffff)]).
  { apply (K12 _ _ (STAT1 _ _ (rw_cells_tail m _ _ _ DK2) ltac:(cbn; clear; lia))); [cbn; clear; lia|]. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply client_static_intro; clear - Hx; lia|].
    unfold ICF_W, IB_W, LS_W; cbn [outside app]. unfold G_IC_BASE_ONCE, G_LS_ONCE, G_IC_OPTSDONE, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET in *.
    clear - Hx HJ0 HJ3. repeat split; lia. }
  Ltac k12j K H HJ0 HJ3 := apply (K _ _ H); [cbn [cells_size csize Nat.add]; clear - HJ0 HJ3; lia | cbn [cells_size csize Nat.add]; intros x Hx; split;
    [apply client_static_intro; clear - Hx HJ0 HJ3; lia | unfold ICF_W, IB_W, LS_W; cbn [outside app]; unfold G_IC_BASE_ONCE, G_LS_ONCE, G_IC_OPTSDONE, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET in *; clear - Hx HJ0 HJ3; repeat split; lia]].
  assert (TVO2 : rw_cells asegs m2 0xb9f4a0 [C4 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ TVO ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (TVR2 : rw_cells asegs m2 0xb9f4c0 [C4 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ TVR ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (TVG2 : rw_cells asegs m2 0xb9f4e0 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ TVG ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (T1_2 : rw_cells asegs m2 (0xbc5298 + 8 * j1) [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ T1 ltac:(cbn [cells_size csize Nat.add]; clear - HJ0 HJ3; lia)) HJ0 HJ3).
  assert (T3_2 : rw_cells asegs m2 (0xbc5298 + 8 * (j1 + 3)) [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ T3 ltac:(cbn [cells_size csize Nat.add]; clear - HJ0 HJ3; lia)) HJ0 HJ3).
  assert (K3_2 : rw_cells asegs m2 (0xbc4e58 + 8 * (j1 + 3)) [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ K3 ltac:(cbn [cells_size csize Nat.add]; clear - HJ0 HJ3; lia)) HJ0 HJ3).
  assert (SEC2 : rw_cells asegs m2 0xb9f860 [C1 (Z_to_bv 8 0)]) by (k12j K12 (STAT1 _ _ SEC ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (DC740_2 : rw_cells asegs m2 0xb9f740 [C4 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ DC740 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (DC720_2 : rw_cells asegs m2 0xb9f720 [C4 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ DC720 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (DC760_2 : rw_cells asegs m2 0xb9f760 [C4 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ DC760 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (DC780_2 : rw_cells asegs m2 0xb9f780 [C4 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ DC780 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (DC7A0_2 : rw_cells asegs m2 0xb9f7a0 [C4 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ DC7A0 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (DC560_2 : rw_cells asegs m2 0xb9f560 [C1 (Z_to_bv 8 0)]) by (k12j K12 (STAT1 _ _ DC560 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (DC580_2 : rw_cells asegs m2 0xb9f580 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ DC580 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (DC588_2 : rw_cells asegs m2 0xb9f588 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ DC588 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (DC5F0_2 : rw_cells asegs m2 0xb9f5f0 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ DC5F0 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X628_2 : rw_cells asegs m2 0xb9f628 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X628 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X630_2 : rw_cells asegs m2 0xb9f630 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X630 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X638_2 : rw_cells asegs m2 0xb9f638 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X638 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X640_2 : rw_cells asegs m2 0xb9f640 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X640 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X648_2 : rw_cells asegs m2 0xb9f648 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X648 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X650_2 : rw_cells asegs m2 0xb9f650 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X650 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X658_2 : rw_cells asegs m2 0xb9f658 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X658 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X660_2 : rw_cells asegs m2 0xb9f660 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X660 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X668_2 : rw_cells asegs m2 0xb9f668 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X668 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X670_2 : rw_cells asegs m2 0xb9f670 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X670 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X678_2 : rw_cells asegs m2 0xb9f678 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X678 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X680_2 : rw_cells asegs m2 0xb9f680 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X680 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X688_2 : rw_cells asegs m2 0xb9f688 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X688 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X690_2 : rw_cells asegs m2 0xb9f690 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X690 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X698_2 : rw_cells asegs m2 0xb9f698 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X698 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X6A0_2 : rw_cells asegs m2 0xb9f6a0 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X6A0 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X6A8_2 : rw_cells asegs m2 0xb9f6a8 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X6A8 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X6B0_2 : rw_cells asegs m2 0xb9f6b0 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X6B0 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (X6B8_2 : rw_cells asegs m2 0xb9f6b8 [C8 (Z_to_bv 64 0)]) by (k12j K12 (STAT1 _ _ X6B8 ltac:(cbn; clear; lia)) HJ0 HJ3).
  assert (FR2 : rw_cells asegs m2 usp1 [CB 8 j8; C8 (Z_to_bv 64 RA_INIT)]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). cbn [cells_size csize Nat.add]. intros x Hx. apply PRES2; [left; clear - Hx NUM; unfold usp1, USTACK_TOP in *; lia|].
    unfold ICF_W, IB_W, LS_W; cbn [outside app]. unfold G_IC_BASE_ONCE, G_LS_ONCE, G_IC_OPTSDONE, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET in *.
    clear - Hx NUM HSTK HJ0 HJ3. unfold usp1, FUZZ_STACK in *. repeat split; lia. }
  (* [comment removed for export] *)
  assert (IN1 : forall e, In e [(pk, 40); (P, 128); (SA, 32); (MK, 72); (p2, 40); (p1, 40)] -> In e (rt_live RT Σ1)).
  { intros e He. eapply Permutation_in; [apply Permutation_sym; exact PERM1|]. apply in_or_app. right. cbn [In] in He |- *. tauto. }
  assert (APT1 : forall pa na pb nb, In (pa, na) (rt_live RT Σ1) -> In (pb, nb) (rt_live RT Σ1) -> (pa, na) <> (pb, nb) -> pa + na <= pb \/ pb + nb <= pa).
  { intros pa na pb nb Ha Hb NE. destruct (in_split _ _ Ha) as (l1 & l2 & EL). apply (af_live_disj RT AF Σ1 m2 pa na pb nb l1 l2 ART2 EL).
    rewrite EL in Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|[Hb|Hb]]; [left; exact Hb | exfalso; exact (NE Hb) | right; exact Hb]. }
  (* [comment removed for export] *)
  pose proof (fi_w1 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 s0 s1 (Z_to_bv 64 1) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 UT2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  rewrite <- CG1 in CGH.
  apply (C_ECL Σ1 PMc (Z_to_bv 64 FI_RET2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 s0 s1 (Z_to_bv 64 1) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
           F2 fc2 m2 lo [] lb' g (j1 + 2) j1 MK SA P z64 top' (zeros 24) (zeros 40) (zeros 120) u' (Z_to_bv 64 0) (Z_to_bv 64 0) oldcb FDO MST eq_refl ART2 MI2).
  { rewrite <- SP1 in LOW. fold usp in SPA. cl_call_ok EU1 ST2 LOW SPA 1. }
  { rewrite EU1. clear - HSTK. unfold usp1, FUZZ_STACK, RT_STACK in *. lia. }
  { rewrite (unsigned_lit FI_RET2) by (unfold FI_RET2; clear; lia). split; [| exact I]. apply (proj2 CGH). wp_in_lit. }
  { cbn [uw_chain]. fold usp in FPI. unfold usp1. replace (usp + -16) with (usp - 16) by (clear; lia). exact FPI. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS1, FRS0. cbn [length]. clear; unfold FRAMES_MAX; lia. }
  { pose proof (Permutation_length PERM1) as LEN1. rewrite app_length in LEN1. cbn [length] in LEN1. clear - Hlen LEN1 LL1. unfold CLI_MAX, FUZZ_LIVE in *. lia. }
  { clear - Hcr CR1. replace (mcost 904) with 0 by reflexivity. unfold INIT_COST in *. lia. }
  { exact CLE2. }
  { exact STP2. } { exact OD2. } { exact BONCE2. } { exact BRET2. } { exact MKO2. } { exact MKK2. } { clear - HJ1 HJ3; lia. } { exact TSK2. }
  { apply IN1; clear; cbn [In]; tauto. } { apply IN1; clear; cbn [In]; tauto. } { apply IN1; clear; cbn [In]; tauto. }
  { exact MK16. } { exact SA16. } { exact P16. }
  { apply (APT1 SA 32 P 128 ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(apply IN1; clear; cbn [In]; tauto)). intros E'; injection E'; clear; lia. }
  { apply (APT1 SA 32 MK 72 ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(apply IN1; clear; cbn [In]; tauto)). intros E'; injection E'; clear; lia. }
  { apply (APT1 P 128 MK 72 ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(apply IN1; clear; cbn [In]; tauto)). intros E'; injection E'; clear; lia. }
  { exact MKC2. } { exact SAC2. } { exact PC2. }
  { exact (proj2 (rw_cells_app m2 0x5a9f20 [C4 (Z_to_bv 64 j1)] [C4 (Z_to_bv 64 0xffffffff)]) (conj DK_2 DK4_2)). }
  { clear - HJ1 HJ3; lia. } { clear; lia. } { exact T1_2. } { exact U2. } { exact TVO2. } { exact TVR2. } { exact TVG2. } { exact CBC2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & E & N & Hh & G & SK & LK & D & u'' & top'' & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2 & E0 & E16 & EUP).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & STP4 & OD4 & BONCE4 & BRET4 & SAC4 & HTOP4 & PC4 & ARR4 & TSD4 & U4 & TVO4 & TVR4 & TVG4 & CBC4
                       & HC4 & NC4 & GC4 & LKC4 & DC4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even FI_RET2) in Hc4' by (unfold FI_RET2; lia).
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & _ & _ & _ & UT4).
  assert (INE2 : In (E, 904) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; right; left; reflexivity).
  (* [comment removed for export] *)
  assert (K24 : forall a cs, rw_cells asegs m2 a cs -> a + Z.of_nat (cells_size cs) <= 0x10007fff8000 ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> client_static x /\ outside (EG_W j1 SA P) x) -> rw_cells asegs m4 a cs).
  { intros a cs H R HO. apply (rw_cells_agree_nw asegs m2 m4 _ _ H). intros x Hx. destruct (HO _ Hx) as [H1 H2]. apply PRES4; [right; left; exact H1 | exact H2]. }
  pose proof (af_live_range RT AF Σ1 m2 SA 32 ART2 ltac:(apply IN1; clear; cbn [In]; tauto)) as (_ & SALO & _). pose proof (af_live_range RT AF Σ1 m2 P 128 ART2 ltac:(apply IN1; clear; cbn [In]; tauto)) as (_ & PLO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 SA 32 ART2 ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(clear; lia)) as SAHI. pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 P 128 ART2 ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(clear; lia)) as PHI.
  Ltac k24 K H SAHI PHI := apply (K _ _ H); [cbn [cells_size csize Nat.add]; clear; lia | cbn [cells_size csize Nat.add]; intros x Hx; split;
    [apply client_static_intro; clear - Hx; lia | unfold EG_W, MTL_W; cbn [outside app]; unfold G_ALLOW_CUST in *; clear - Hx SAHI PHI; repeat split; lia]].
  Ltac k24j K H SAHI PHI HJ0 HJ3 := apply (K _ _ H); [cbn [cells_size csize Nat.add]; clear - HJ0 HJ3; lia | cbn [cells_size csize Nat.add]; intros x Hx; split;
    [apply client_static_intro; clear - Hx HJ0 HJ3; lia | unfold EG_W, MTL_W; cbn [outside app]; unfold G_ALLOW_CUST in *; clear - Hx SAHI PHI HJ0 HJ3; repeat split; lia]].
  assert (NK4 : rw_cells asegs m4 0xbc5258 [C4 (Z_to_bv 64 (j1 + 2))]) by (k24j K24 NK2 SAHI PHI HJ0 HJ3).
  assert (KL4 : rw_cells asegs m4 0xbc5260 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 sh]) by (k24j K24 KL2 SAHI PHI HJ0 HJ3).
  assert (KD2_4 : rw_cells asegs m4 (0xbc4e58 + 8 * (j1 + 2)) [C8 (Z_to_bv 64 0x1f69dc)]) by (k24j K24 KD2 SAHI PHI HJ0 HJ3).
  assert (K3_4 : rw_cells asegs m4 (0xbc4e58 + 8 * (j1 + 3)) [C8 (Z_to_bv 64 0)]) by (k24j K24 K3_2 SAHI PHI HJ0 HJ3).
  assert (T3_4 : rw_cells asegs m4 (0xbc5298 + 8 * (j1 + 3)) [C8 (Z_to_bv 64 0)]) by (k24j K24 T3_2 SAHI PHI HJ0 HJ3).
  assert (SEC4 : rw_cells asegs m4 0xb9f860 [C1 (Z_to_bv 8 0)]) by (k24j K24 SEC2 SAHI PHI HJ0 HJ3).
  assert (MKO4 : rw_cells asegs m4 0xb9f500 [C4 (Z_to_bv 64 2)]) by (k24j K24 MKO2 SAHI PHI HJ0 HJ3).
  assert (MKK4 : rw_cells asegs m4 0xb9f520 [C4 (Z_to_bv 64 (j1 + 2))]) by (k24j K24 MKK2 SAHI PHI HJ0 HJ3).
  assert (TSK4 : rw_cells asegs m4 (0xbc5298 + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK)]) by (k24j K24 TSK2 SAHI PHI HJ0 HJ3).
  assert (DC740_4 : rw_cells asegs m4 0xb9f740 [C4 (Z_to_bv 64 0)]) by (k24j K24 DC740_2 SAHI PHI HJ0 HJ3).
  assert (DC720_4 : rw_cells asegs m4 0xb9f720 [C4 (Z_to_bv 64 0)]) by (k24j K24 DC720_2 SAHI PHI HJ0 HJ3).
  assert (DC760_4 : rw_cells asegs m4 0xb9f760 [C4 (Z_to_bv 64 0)]) by (k24j K24 DC760_2 SAHI PHI HJ0 HJ3).
  assert (DC780_4 : rw_cells asegs m4 0xb9f780 [C4 (Z_to_bv 64 0)]) by (k24j K24 DC780_2 SAHI PHI HJ0 HJ3).
  assert (DC7A0_4 : rw_cells asegs m4 0xb9f7a0 [C4 (Z_to_bv 64 0)]) by (k24j K24 DC7A0_2 SAHI PHI HJ0 HJ3).
  assert (DC560_4 : rw_cells asegs m4 0xb9f560 [C1 (Z_to_bv 8 0)]) by (k24j K24 DC560_2 SAHI PHI HJ0 HJ3).
  assert (DC580_4 : rw_cells asegs m4 0xb9f580 [C8 (Z_to_bv 64 0)]) by (k24j K24 DC580_2 SAHI PHI HJ0 HJ3).
  assert (DC588_4 : rw_cells asegs m4 0xb9f588 [C8 (Z_to_bv 64 0)]) by (k24j K24 DC588_2 SAHI PHI HJ0 HJ3).
  assert (DC5F0_4 : rw_cells asegs m4 0xb9f5f0 [C8 (Z_to_bv 64 0)]) by (k24j K24 DC5F0_2 SAHI PHI HJ0 HJ3).
  assert (X628_4 : rw_cells asegs m4 0xb9f628 [C8 (Z_to_bv 64 0)]) by (k24j K24 X628_2 SAHI PHI HJ0 HJ3).
  assert (X630_4 : rw_cells asegs m4 0xb9f630 [C8 (Z_to_bv 64 0)]) by (k24j K24 X630_2 SAHI PHI HJ0 HJ3).
  assert (X638_4 : rw_cells asegs m4 0xb9f638 [C8 (Z_to_bv 64 0)]) by (k24j K24 X638_2 SAHI PHI HJ0 HJ3).
  assert (X640_4 : rw_cells asegs m4 0xb9f640 [C8 (Z_to_bv 64 0)]) by (k24j K24 X640_2 SAHI PHI HJ0 HJ3).
  assert (X648_4 : rw_cells asegs m4 0xb9f648 [C8 (Z_to_bv 64 0)]) by (k24j K24 X648_2 SAHI PHI HJ0 HJ3).
  assert (X650_4 : rw_cells asegs m4 0xb9f650 [C8 (Z_to_bv 64 0)]) by (k24j K24 X650_2 SAHI PHI HJ0 HJ3).
  assert (X658_4 : rw_cells asegs m4 0xb9f658 [C8 (Z_to_bv 64 0)]) by (k24j K24 X658_2 SAHI PHI HJ0 HJ3).
  assert (X660_4 : rw_cells asegs m4 0xb9f660 [C8 (Z_to_bv 64 0)]) by (k24j K24 X660_2 SAHI PHI HJ0 HJ3).
  assert (X668_4 : rw_cells asegs m4 0xb9f668 [C8 (Z_to_bv 64 0)]) by (k24j K24 X668_2 SAHI PHI HJ0 HJ3).
  assert (X670_4 : rw_cells asegs m4 0xb9f670 [C8 (Z_to_bv 64 0)]) by (k24j K24 X670_2 SAHI PHI HJ0 HJ3).
  assert (X678_4 : rw_cells asegs m4 0xb9f678 [C8 (Z_to_bv 64 0)]) by (k24j K24 X678_2 SAHI PHI HJ0 HJ3).
  assert (X680_4 : rw_cells asegs m4 0xb9f680 [C8 (Z_to_bv 64 0)]) by (k24j K24 X680_2 SAHI PHI HJ0 HJ3).
  assert (X688_4 : rw_cells asegs m4 0xb9f688 [C8 (Z_to_bv 64 0)]) by (k24j K24 X688_2 SAHI PHI HJ0 HJ3).
  assert (X690_4 : rw_cells asegs m4 0xb9f690 [C8 (Z_to_bv 64 0)]) by (k24j K24 X690_2 SAHI PHI HJ0 HJ3).
  assert (X698_4 : rw_cells asegs m4 0xb9f698 [C8 (Z_to_bv 64 0)]) by (k24j K24 X698_2 SAHI PHI HJ0 HJ3).
  assert (X6A0_4 : rw_cells asegs m4 0xb9f6a0 [C8 (Z_to_bv 64 0)]) by (k24j K24 X6A0_2 SAHI PHI HJ0 HJ3).
  assert (X6A8_4 : rw_cells asegs m4 0xb9f6a8 [C8 (Z_to_bv 64 0)]) by (k24j K24 X6A8_2 SAHI PHI HJ0 HJ3).
  assert (X6B0_4 : rw_cells asegs m4 0xb9f6b0 [C8 (Z_to_bv 64 0)]) by (k24j K24 X6B0_2 SAHI PHI HJ0 HJ3).
  assert (X6B8_4 : rw_cells asegs m4 0xb9f6b8 [C8 (Z_to_bv 64 0)]) by (k24j K24 X6B8_2 SAHI PHI HJ0 HJ3).
  assert (MKC4 : rw_cells asegs m4 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ MKC2). cbn [cells_size csize Nat.add]. intros x Hx.
    pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 MK 72 ART2 ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(clear; lia)) as MKHI.
    pose proof (APT1 SA 32 MK 72 ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(intros E'; injection E'; clear; lia)) as D1.
    pose proof (APT1 P 128 MK 72 ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(intros E'; injection E'; clear; lia)) as D2.
    apply PRES4; [right; right; left; exists MK, 72; split; [apply IN1; clear; cbn [In]; tauto | clear - Hx; lia]|].
    unfold EG_W, MTL_W; cbn [outside app]. unfold G_ALLOW_CUST in *. clear - Hx MKHI D1 D2 HJ0 HJ3. repeat split; lia. }
  assert (FR4 : rw_cells asegs m4 usp1 [CB 8 j8; C8 (Z_to_bv 64 RA_INIT)]).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ FR2). cbn [cells_size csize Nat.add]. intros x Hx. apply PRES4; [left; clear - Hx NUM; unfold usp1, USTACK_TOP in *; lia|].
    unfold EG_W, MTL_W; cbn [outside app]. unfold G_ALLOW_CUST in *. rewrite SP1 in SALO, PLO. clear - Hx NUM HSTK HJ0 HJ3 SALO PLO LOW. unfold usp1, FUZZ_STACK in *. repeat split; lia. }
  (* [comment removed for export] *)
  pose proof (fi_w2 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) v0 v1 v2 s0 s1 (Z_to_bv 64 (E + 896)) d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 UT4) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & <- & Hc5'). clear Hc5.
  (* [comment removed for export] *)
  rewrite <- CG2 in CGH.
  apply (C_FXI Σ2 PMc (Z_to_bv 64 FI_RET3) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) v0 v1 v2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
           F4 fc4 m4 lo [] (Z_to_bv 8 1) g (j1 + 2) (j1 + 3) sh (Z_to_bv 64 0) (Z_to_bv 64 0x1f69dc) (Z_to_bv 64 0) oldcb (Z_to_bv 8 0) (Z_to_bv 64 0)
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 OPT_LOAD_STRINGS)
           FDO MST eq_refl eq_refl eq_refl ART4 MI4).
  { rewrite <- SP1, <- SP2 in LOW. fold usp in SPA. cl_call_ok EU1 ST4 LOW SPA 1. }
  { rewrite EU1. clear - HSTK. unfold usp1, FUZZ_STACK, RT_STACK in *. lia. }
  { rewrite (unsigned_lit FI_RET3) by (unfold FI_RET3; clear; lia). split; [| exact I]. apply (proj2 CGH). wp_in_lit. }
  { rewrite (unsigned_lit FI_RET3) by (unfold FI_RET3; clear; lia). apply (proj2 CGH). wp_in_lit. }
  { cbn [uw_chain]. fold usp in FPI. unfold usp1. replace (usp + -16) with (usp - 16) by (clear; lia). exact FPI. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite FRS2, FRS1, FRS0. cbn [length]. clear; unfold FRAMES_MAX; lia. }
  { pose proof (Permutation_length PERM1) as LEN1. rewrite app_length in LEN1. cbn [length] in LEN1. rewrite LV2. rewrite app_length. cbn [length]. clear - Hlen LEN1 LL1. unfold CLI_MAX, FUZZ_LIVE in *. lia. }
  { assert (GC : GDC_COST <= 2^16) by (vm_compute; intros HH; discriminate HH).
    clear - Hcr CR1 CR2 GC. replace (mcost 904) with 0 in CR2 by reflexivity. unfold INIT_COST in *. lia. }
  { (* [comment removed for export] *)
    rewrite LV2. apply Forall_app. split; [repeat (apply Forall_cons; [cbn [snd]; clear; lia|]); apply Forall_nil|].
    apply Forall_cons; [cbn [snd]; clear; lia|].
    apply Forall_forall. intros [p n] Hin. cbn [snd]. pose proof (Permutation_in _ PERM1 Hin) as Hin'.
    apply in_app_or in Hin' as [Hin'|Hin']; [exact (lh_repE_pos _ _ _ _ _ _ _ REP2 p n Hin')|].
    cbn [In] in Hin'. repeat (destruct Hin' as [EQ|Hin']; [injection EQ; clear; lia|]). exact (POS p n Hin'). }
  { exact CLE4. }
  { exact DC740_4. } { exact DC780_4. } { exact DC720_4. } { exact DC760_4. } { exact NK4. } { clear - HJ1 HJ3; lia. } { exact KL4. }
  { exact K3_4. } { exact (wg_rw_ro _ _ _ KD2_4). }
  { right. split; [rewrite Z.mod_small by (clear - HJ1 HJ3; lia); clear; lia | rewrite unsigned_lit by (clear; lia); clear; lia]. }
  { exact T3_4. } { exact CBC4. } { exact DC5F0_4. }
  { exact DC560_4. } { exact DC7A0_4. } { exact DC580_4. }
  { exact X628_4. } { exact X630_4. } { exact X638_4. } { exact X640_4. } { exact X648_4. } { exact X650_4. } { exact X658_4. } { exact X660_4. } { exact X668_4. } { exact X670_4. }
  { exact X678_4. } { exact X680_4. } { exact X688_4. } { exact X690_4. } { exact X698_4. } { exact X6A0_4. } { exact X6A8_4. } { exact X6B0_4. } { exact X6B8_4. }
  { exact DC588_4. } { exact STP4. } { exact OD4. } { exact BONCE4. } { exact BRET4. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & lk & Hc6 & DCB & HJ & LK16 & FRS3 & SP3 & CR3 & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & ST6) & PRES6 & CLE6 & O1 & O2 & DCK & DCR & NK6 & KL6 & KJ6 & TSDJ & CBC6 & IP12 & INLK & GLK & LKC6 & DR2 & DIN & STP6 & BONCE6 & BRET6) & Hc6'). clear Hc6.
  destruct RS6 as (w0 & w1 & w2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even FI_RET3) in Hc6' by (unfold FI_RET3; lia).
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & _ & _ & _ & UT6).
  assert (FR6 : rw_cells asegs m6 usp1 [CB 8 j8; C8 (Z_to_bv 64 RA_INIT)]).
  { apply (rw_cells_agree_nw asegs m4 m6 _ _ FR4). cbn [cells_size csize Nat.add]. intros x Hx. apply PRES6; [left; clear - Hx NUM; unfold usp1, USTACK_TOP in *; lia|].
    unfold GDC_W; cbn [outside app]. unfold G_ALLOW_CUST in *. clear - Hx NUM HSTK HJ. unfold usp1, FUZZ_STACK in *. repeat split; lia. }
  (* [comment removed for export] *)
  pose proof (fi_w3 sp gp (Z_to_bv 64 TP_A) w0 w1 w2 s0 s1 (Z_to_bv 64 0) h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 (Z_to_bv 64 FI_RET3) (Z_to_bv 64 RA_INIT) j8 F6 fc6 m6 lo) as W3.
  fold usp in W3. fold usp1 in W3.
  specialize (W3 ST6 ltac:(clear - NUM; lia) ltac:(clear - HSTK; unfold FUZZ_STACK in *; lia) ltac:(clear - NUM; lia) UT6 FR6 MI6).
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (-> & ST7) & Hc7'). clear Hc7.
  fold usp in ST7.
  (* [comment removed for export] *)
  destruct DCB as (news & LV3 & LEN3 & FA3 & INN).
  set (ECL7 := [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (Hh, 8); (E, 904)]).
  set (ICF6 := [(pk, 40); (P, 128); (SA, 32); (MK, 72); (p2, 40); (p1, 40)]).
  apply Hk. exists Σ3, (news ++ ECL7 ++ L' ++ ICF6).
  assert (PERM3 : Permutation (rt_live RT Σ3) ((news ++ ECL7 ++ L' ++ ICF6) ++ rt_live RT Σ)).
  { rewrite LV3, LV2. unfold ECL7, ICF6. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. do 7 apply perm_skip. exact PERM1. }
  split; [| split; [exact PERM3 | split; [| split; [| split; [rewrite FRS3, FRS2, FRS1; exact FRS0 | split; [rewrite SP3, SP2; exact SP1 | split; [| rewrite CG3, CG2; exact CG1]]]]]]].
  2:{ rewrite !app_length. unfold ECL7, ICF6. cbn [length]. clear - LEN3 LL1. unfold CLI_MAX. lia. }
  2:{ intros p n Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (proj2 (proj2 (proj2 (proj1 (Forall_forall _ _) FA3 _ Hin))))|].
      apply in_app_or in Hin as [Hin|Hin]; [unfold ECL7 in Hin; cbn [In] in Hin; repeat (destruct Hin as [EQ|Hin]; [injection EQ; clear; lia|]); destruct Hin|].
      apply in_app_or in Hin as [Hin|Hin]; [exact (lh_repE_pos _ _ _ _ _ _ _ REP2 p n Hin)|].
      unfold ICF6 in Hin; cbn [In] in Hin; repeat (destruct Hin as [EQ|Hin]; [injection EQ; clear; lia|]); destruct Hin. }
  2:{ clear - Hcr CR1 CR2 CR3. assert (GC : GDC_COST <= 2^16) by (vm_compute; intros HH; discriminate HH). pose proof GDC_COST_nonneg. replace (mcost 904) with 0 in CR2 by reflexivity. unfold INIT_COST in *. lia. }
  (* [comment removed for export] *)
  assert (PERMSA : Permutation (rt_live RT Σ1) ((SA, 32) :: ((L' ++ [(pk, 40); (P, 128)]) ++ (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ))).
  { eapply Permutation_trans; [exact PERM1|].
    replace (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ)
      with ((L' ++ [(pk, 40); (P, 128)]) ++ (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ) by (rewrite <- app_assoc; reflexivity).
    apply Permutation_sym. apply Permutation_middle. }
  assert (PERMP : Permutation (rt_live RT Σ1) ((P, 128) :: ((L' ++ [(pk, 40)]) ++ (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ))).
  { eapply Permutation_trans; [exact PERM1|].
    replace (L' ++ (pk, 40) :: (P, 128) :: (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ)
      with ((L' ++ [(pk, 40)]) ++ (P, 128) :: (SA, 32) :: (MK, 72) :: (p2, 40) :: (p1, 40) :: rt_live RT Σ) by (rewrite <- app_assoc; reflexivity).
    apply Permutation_sym. apply Permutation_middle. }
  destruct (in_split _ _ INN) as (n1 & n2 & EN).
  assert (PERMLK : Permutation (rt_live RT Σ3) ((lk, 40) :: (n1 ++ n2 ++ rt_live RT Σ2))).
  { rewrite LV3, EN, <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
  assert (IN2 : forall e, In e (rt_live RT Σ1) -> In e (rt_live RT Σ2)) by (intros x Hx; rewrite LV2; apply in_or_app; right; right; exact Hx).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 lk 40 ART6 INLK ltac:(clear; lia)) as LKHI.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 MK 72 ART2 ltac:(apply IN1; clear; cbn [In]; tauto) ltac:(clear; lia)) as MKHI.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 E 904 ART4 INE2 ltac:(clear; lia)) as EHI.
  (* [comment removed for export] *)
  assert (GDCS : forall x, 0x10007fff8000 <= x -> outside (GDC_W (j1 + 3)) x).
  { intros x Hx. unfold GDC_W; cbn [outside app]. unfold G_ALLOW_CUST. clear - Hx HJ. repeat split; lia. }
  assert (K46s : forall a cs, rw_cells asegs m4 a cs -> (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5698) ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> outside (GDC_W (j1 + 3)) x) -> rw_cells asegs m6 a cs).
  { intros a cs H R HO. apply (rw_cells_agree_nw asegs m4 m6 _ _ H). intros x Hx. apply PRES6; [right; left; apply client_static_intro; clear - R Hx; lia | exact (HO _ Hx)]. }
  assert (K46h : forall a cs p n, rw_cells asegs m4 a cs -> In (p, n) (rt_live RT Σ2) -> n <= 64512 -> p <= a -> a + Z.of_nat (cells_size cs) <= p + n -> rw_cells asegs m6 a cs).
  { intros a cs p n H Hin HN H1 H2. pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 p n ART4 Hin HN) as PHI'.
    apply (rw_cells_agree_nw asegs m4 m6 _ _ H). intros x Hx. apply PRES6; [right; right; left; exists p, n; split; [exact Hin | clear - Hx H1 H2; lia] | apply GDCS; clear - Hx H1 PHI'; lia]. }
  Ltac gdcw HJ := unfold GDC_W; cbn [cells_size csize Nat.add outside app]; unfold G_ALLOW_CUST; intros x Hx; clear - Hx HJ; repeat split; lia.
  assert (OD6 : rw_cells asegs m6 G_IC_OPTSDONE [C8 (Z_to_bv 64 OPT_LOAD_STRINGS)]) by (apply (K46s _ _ OD4); [unfold G_IC_OPTSDONE; cbn [cells_size csize Nat.add]; clear; lia | unfold G_IC_OPTSDONE; gdcw HJ]).
  assert (SEC6 : rw_cells asegs m6 0xb9f860 [C1 (Z_to_bv 8 0)]) by (apply (K46s _ _ SEC4); [cbn [cells_size csize Nat.add]; clear; lia | gdcw HJ]).
  assert (MKO6 : rw_cells asegs m6 0xb9f500 [C4 (Z_to_bv 64 2)]) by (apply (K46s _ _ MKO4); [cbn [cells_size csize Nat.add]; clear; lia | gdcw HJ]).
  assert (MKK6 : rw_cells asegs m6 0xb9f520 [C4 (Z_to_bv 64 (j1 + 2))]) by (apply (K46s _ _ MKK4); [cbn [cells_size csize Nat.add]; clear; lia | gdcw HJ]).
  assert (TSK6 : rw_cells asegs m6 (0xbc5298 + 8 * (j1 + 2)) [C8 (Z_to_bv 64 MK)]) by (apply (K46s _ _ TSK4); [cbn [cells_size csize Nat.add]; clear - HJ0 HJ3; lia | gdcw HJ]).
  assert (ERR6 : rw_cells asegs m6 0xba3e4c [C4 e']).
  { apply (K46s _ _ ltac:(apply (K24 _ _ ERR2); [cbn; clear; lia | cbn [cells_size csize Nat.add]; intros x Hx; split; [apply client_static_intro; clear - Hx; lia | unfold EG_W, MTL_W; cbn [outside app]; unfold G_ALLOW_CUST in *; clear - Hx SAHI PHI HJ0; repeat split; lia]]));
      [cbn [cells_size csize Nat.add]; clear; lia | gdcw HJ]. }
  assert (MKC6 : rw_cells asegs m6 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]) by (apply (K46h _ _ MK 72 MKC4 (IN2 (MK, 72) ltac:(apply IN1; clear; cbn [In]; tauto)) ltac:(clear; lia)); [clear; lia | cbn [cells_size csize Nat.add]; clear; lia]).
  assert (SAC6 : rw_cells asegs m6 SA (sa_hdr (Z_to_bv 64 1) z64 top'' (Z_to_bv 64 1) (Z_to_bv 64 P))) by (apply (K46h _ _ SA 32 SAC4 (IN2 (SA, 32) ltac:(apply IN1; clear; cbn [In]; tauto)) ltac:(clear; lia)); [clear; lia | unfold sa_hdr; cbn [cells_size csize Nat.add]; clear; lia]).
  assert (PC6 : rw_cells asegs m6 P [C8 (Z_to_bv 64 E); CB 120 (zeros 120)]) by (apply (K46h _ _ P 128 PC4 (IN2 (P, 128) ltac:(apply IN1; clear; cbn [In]; tauto)) ltac:(clear; lia)); [clear; lia | cbn [cells_size csize Nat.add]; clear; lia]).
  assert (ARR6 : ecl_arrs m6 E 16).
  { assert (KE : forall a cs, rw_cells asegs m4 a cs -> E <= a -> a + Z.of_nat (cells_size cs) <= E + 904 -> rw_cells asegs m6 a cs) by (intros a cs H H1 H2; exact (K46h a cs E 904 H INE2 ltac:(clear; lia) H1 H2)).
    destruct ARR4 as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9). unfold ecl_arrs. cbn [Nat.sub repeat app] in R0, R1, R2, R3, R4, R5, R6, R7, R8 |- *.
    Ltac ke KE R := exact (KE _ _ R ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add repeat app]; clear; lia)).
    split; [ke KE R0|]. split; [ke KE R1|]. split; [ke KE R2|]. split; [ke KE R3|]. split; [ke KE R4|]. split; [ke KE R5|]. split; [ke KE R6|]. split; [ke KE R7|]. split; [ke KE R8| ke KE R9]. }
  (* [comment removed for export] *)
  eapply ASTA_conseq; [exact Hc7'|]. intros ms <-. exists m6.
  split; [exists w0, w1, w2, h1, h2, h3, h4, h5, h6, h7, w3, w4, w5, w6, F6, fc6; reflexivity|].
  split; [exact (conj ART6 (conj MI6 ST7))|].
  split.
  { (* [comment removed for export] *)
    intros a Ha Ho.
    assert (A0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)) by (rewrite FRS0; exact Ha).
    pose proof (cl_split RT AF Σ m usp 16 _ ART0 ltac:(clear - NUM; unfold FUZZ_STACK in *; lia) ltac:(clear; lia) A0) as SPL.
    assert (A1 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A0); [auto | auto | clear; unfold usp1; lia]).
    assert (A2 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ A1); [intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM1 | apply in_or_app; right; do 6 right; exact Hx] | rewrite FRS1; auto | clear; lia]. }
    assert (A3 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ A2); [exact IN2 | rewrite FRS2; auto | clear; lia]).
    (* [comment removed for export] *)
    assert (COVER : forall W : list (Z * Z), (forall lo hi, In (lo, hi) W -> (exists lo' hi', In (lo', hi') LIB_W /\ lo' <= lo /\ hi <= hi') \/ ~ (lo <= bv_unsigned a < hi)) -> outside W (bv_unsigned a))
      by (intros W HW; exact (outside_cover LIB_W W (bv_unsigned a) Ho HW)).
    Ltac libw1 LO HI HJ0 HJ3 := exists LO, HI; split; [clear; unfold LIB_W; cbn [In]; tauto | clear - HJ0 HJ3; lia].
    Ltac libw HJ0 HJ3 := left; first
      [ libw1 0x5a9f20 0x5a9f24 HJ0 HJ3 | libw1 0xb9f1c0 0xb9f1e0 HJ0 HJ3 | libw1 0xb9f200 0xb9f848 HJ0 HJ3 | libw1 0xba3e4c 0xba3e50 HJ0 HJ3
      | libw1 0xba3e5a 0xba3e5b HJ0 HJ3 | libw1 0xba3e90 0xba3e98 HJ0 HJ3 | libw1 0xbc4e60 0xbc5268 HJ0 HJ3 | libw1 0xbc52a0 0xbc5698 HJ0 HJ3 ].
    (* [comment removed for export] *)
    pose proof (af_live_range RT AF Σ1 m2 SA 32 ART2 ltac:(apply IN1; clear; cbn [In]; tauto)) as (_ & SALO' & _). pose proof (af_live_range RT AF Σ1 m2 P 128 ART2 ltac:(apply IN1; clear; cbn [In]; tauto)) as (_ & PLO' & _).
    rewrite SP1 in SALO', PLO'.
    assert (NSA : ~ (SA <= bv_unsigned a < SA + 32)).
    { destruct A0 as [H|[H|[H|[H|H]]]].
      - clear - H SALO' LOW HSTK. unfold FUZZ_STACK in *. lia.
      - pose proof (client_static_range _ H). clear - H0 SAHI. unfold SEGTOP_A in *. lia.
      - destruct H as (p & n & Hin & Hp). pose proof (perm_live_apartF RT AF Σ1 m2 (SA, 32) _ (p, n) ART2 PERMSA ltac:(apply in_or_app; right; do 3 right; exact Hin)) as DJ. cbn [fst snd] in DJ. clear - DJ Hp. lia.
      - rewrite FRS0 in H. destruct H as (f & k & [] & _).
      - rewrite FRS0 in H. destruct H as (f & k & [] & _). }
    assert (NP : ~ (P <= bv_unsigned a < P + 128)).
    { destruct A0 as [H|[H|[H|[H|H]]]].
      - clear - H PLO' LOW HSTK. unfold FUZZ_STACK in *. lia.
      - pose proof (client_static_range _ H). clear - H0 PHI. unfold SEGTOP_A in *. lia.
      - destruct H as (p & n & Hin & Hp). pose proof (perm_live_apartF RT AF Σ1 m2 (P, 128) _ (p, n) ART2 PERMP ltac:(apply in_or_app; right; do 4 right; exact Hin)) as DJ. cbn [fst snd] in DJ. clear - DJ Hp. lia.
      - rewrite FRS0 in H. destruct H as (f & k & [] & _).
      - rewrite FRS0 in H. destruct H as (f & k & [] & _). }
    rewrite (PRES6 a A3); [| apply COVER; unfold GDC_W, G_ALLOW_CUST; cbn [In app]; intros wl wh Hin;
      repeat (destruct Hin as [EQ|Hin]; [injection EQ as <- <-; libw HJ0 HJ3 |]); destruct Hin].
    rewrite (PRES4 a A2); [| apply COVER; unfold EG_W, MTL_W, G_ALLOW_CUST; cbn [In app]; intros wl wh Hin;
      destruct Hin as [EQ|Hin]; [injection EQ as <- <-; right; clear - NSA; lia|];
      destruct Hin as [EQ|Hin]; [injection EQ as <- <-; right; clear - NP; lia|];
      repeat (destruct Hin as [EQ|Hin]; [injection EQ as <- <-; libw HJ0 HJ3 |]); destruct Hin].
    rewrite (PRES2 a A1); [| apply COVER; unfold ICF_W, IB_W, LS_W, G_IC_BASE_ONCE, G_LS_ONCE, G_IC_OPTSDONE, G_ALLOW_CUST, G_IC_OPTS_LOCK, G_IC_INIT_LOCK, G_IC_IICL_KEY, G_IC_BASE_INITED, G_IC_BASE_RET, G_ERR_ONCE, G_ERR_LOCK, G_ERR_HASH, G_ERR_FLAG, G_LS_RET;
      cbn [In app]; intros wl wh Hin; repeat (destruct Hin as [EQ|Hin]; [injection EQ as <- <-; libw HJ0 HJ3 |]); destruct Hin].
    exact (PR1 a A0 I). }
  split.
  { (* [comment removed for export] *)
    split; [exact (proj1 CLE6)|]. split; [exact (cl_env_lat _ _ _ CLE6)|]. split; [exact SEC6|].
    exists E, [(MK, 72); (SA, 32); (P, 128); (lk, 40)]. split; [| split; [| split; [| split]]].
    - exists (Z_to_bv 64 OPT_LOAD_STRINGS), (j1 + 2), MK, SA, P, 1, (Z_to_bv 64 0), top'', (Z_to_bv 64 1), (j1 + 3), lk. split; [reflexivity|].
      split; [exact (conj STP6 (conj OD6 (conj BONCE6 BRET6)))|].
      split.
      { split; [exact MKO6|]. split; [exact MKK6|]. split; [clear - HJ1 HJ3; lia|]. split; [exact TSK6|].
        split; [pose proof (rw_cells_skip m6 MK [CB 24 (zeros 24)] [C8 (Z_to_bv 64 SA); CB 40 (zeros 40)] MKC6) as H; cbn [cells_size csize Nat.add] in H; exact (rw_cells_head m6 _ _ _ H)|].
        split; [exact SAC6|]. split; [rewrite unsigned_lit by (clear; lia); clear; lia|]. split; [clear; lia|]. exact (rw_cells_head m6 _ _ _ PC6). }
      split; [clear - MK16; Z.div_mod_to_equations; lia|]. split; [clear - SA16; Z.div_mod_to_equations; lia|]. split; [clear - P16; Z.div_mod_to_equations; lia|].
      split; [clear - E16; Z.div_mod_to_equations; lia|].
      split.
      { split; [exact (wg_rw_ro _ _ _ DIN)|]. split; [exact (wg_rw_ro _ _ _ DCK)|]. split; [clear - HJ1 HJ3; lia|].
        split; [exact (wg_rw_ro _ _ _ O1)|]. split; [exact (wg_rw_ro _ _ _ DCR)|]. split; [exact (wg_rw_ro _ _ _ O2)|]. split; [exact (wg_rw_ro _ _ _ DR2)|].
        split; [exact (wg_rw_ro _ _ _ TSDJ)|]. split; [exact (wg_rw_ro _ _ _ GLK)|]. split; [exact LK16|]. exact (wg_rw_ro _ _ _ IP12). }
      split; [exact LKC6|]. split; [clear - LKHI; lia|].
      assert (APL : forall p n, In (p, n) (rt_live RT Σ1) -> lk + 40 <= p \/ p + n <= lk).
      { intros p n Hin. pose proof (perm_live_apartF RT AF Σ3 m6 (lk, 40) _ (p, n) ART6 PERMLK ltac:(apply in_or_app; right; apply in_or_app; right; exact (IN2 _ Hin))) as DJ. cbn [fst snd] in DJ. exact DJ. }
      split; [exact (APL MK 72 ltac:(apply IN1; clear; cbn [In]; tauto))|]. split; [exact (APL SA 32 ltac:(apply IN1; clear; cbn [In]; tauto))|]. exact (APL P 128 ltac:(apply IN1; clear; cbn [In]; tauto)).
    - split; [reflexivity|]. exact (es_at_rest_of_arrs m6 E ARR6).
    - apply in_or_app. right. apply in_or_app. left. unfold ECL7. cbn [In]. tauto.
    - intros x Hx. cbn [In] in Hx. destruct Hx as [<-|[<-|[<-|[<-|[]]]]].
      + apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. unfold ICF6; cbn [In]; tauto.
      + apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. unfold ICF6; cbn [In]; tauto.
      + apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. unfold ICF6; cbn [In]; tauto.
      + apply in_or_app; left. exact INN.
    - cbn [In]. intros [EQ|[EQ|[EQ|[EQ|[]]]]]; injection EQ; clear; lia. }
  exists e'. unfold errno_cell. rewrite unsigned_lit by (clear; lia). exact ERR6.
Qed.
End Finit.
