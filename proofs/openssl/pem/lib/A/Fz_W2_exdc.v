(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Th_mutex Fz_M_free Fz_T_lock Fz_W1_defs Fz_W3_iface Fz_W5_rep Fz_W2_exdl Fz_W2_exd Fz_W2_exds Fz_W2_exdx Fz_W2_exdf Fz_W2_exdfs Fz_W2_exdfx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nx_w_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem),
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_new_ex_data_ex) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_new_ex_data) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST GLO LO SPH MI. unfold e_new_ex_data, e_new_ex_data_ex in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. th_release FR (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exd_stat (m : mem) (kd LK : Z) : Prop :=
     ro_cells asegs m DC_INITED [C1 (Z_to_bv 8 1)] /\ ro_cells asegs m DC_KEY [C4 (wz kd)] /\ 1 <= kd < 128
  /\ ro_cells asegs m DC_ONCE1 [C4 (wz 2)] /\ ro_cells asegs m DC_RET1 [C4 (wz 1)]
  /\ ro_cells asegs m DC_ONCE2 [C4 (wz 2)] /\ ro_cells asegs m DC_RET2 [C4 (wz 1)]
  /\ ro_cells asegs m (0xbc5298 + 8 * kd) [C8 z64]
  /\ ro_cells asegs m DC_GLOBAL_LOCK [C8 (wz LK)] /\ LK mod 16 = 0
  /\ ro_cells asegs m DC_IP12 [C8 z64].
Definition exd_fp (kd a : Z) : Prop := (0xb9f560 <= a < 0xb9f7a8) \/ (0xbc5298 + 8 * kd <= a < 0xbc5298 + 8 * kd + 8).

Lemma exd_stat_agree : forall (m m' : mem) kd LK, exd_stat m kd LK -> agree_on (exd_fp kd) m m' -> exd_stat m' kd LK.
Proof.
  intros m m' kd LK (A1 & A2 & KD & A3 & A4 & A5 & A6 & A7 & A8 & LKAL & A9) AG.
  unfold exd_stat, DC_INITED, DC_KEY, DC_ONCE1, DC_RET1, DC_ONCE2, DC_RET2, DC_GLOBAL_LOCK, DC_IP12, DC_CTX in *.
  assert (R : forall a cs, ro_cells asegs m a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> exd_fp kd x) -> ro_cells asegs m' a cs).
  { intros a cs H HR. apply (ro_cells_agree asegs m m' a cs H). intros x Hx. apply AG. exact (HR _ Hx). }
  unfold exd_fp in R.
  split; [apply (R _ _ A1); cbn; intros; lia|]. split; [apply (R _ _ A2); cbn; intros; lia|]. split; [exact KD|].
  split; [apply (R _ _ A3); cbn; intros; lia|]. split; [apply (R _ _ A4); cbn; intros; lia|].
  split; [apply (R _ _ A5); cbn; intros; lia|]. split; [apply (R _ _ A6); cbn; intros; lia|].
  split; [apply (R _ _ A7); cbn; intros; lia|].
  split; [apply (R _ _ A8); cbn; intros; lia|]. split; [exact LKAL|]. apply (R _ _ A9); cbn; intros; lia.
Qed.

Lemma exd_fp_static : forall kd a, 1 <= kd < 128 -> exd_fp kd a -> client_static a.
Proof. intros kd a KD [H|H]; apply client_static_intro; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition c8s (cs : list cell) : Prop := Forall (fun c => csize c = 8%nat) cs.
Lemma sz_low11 : forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10, c8s [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] -> cells_size [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] = 88%nat.
Proof.
  intros until c10. intros H8. unfold c8s in H8.
  repeat (apply Forall_cons_iff in H8; let E := fresh "E" in destruct H8 as [E H8]). cbn [cells_size]. lia.
Qed.
Lemma sz_nxb : forall pd c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 g1 g2 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 r,
  (pd = 0 \/ pd = 16) -> c8s [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ->
  Z.of_nat (cells_size (nxb_frame pd c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 g1 g2 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 r)) = 192 + pd.
Proof.
  intros until r. intros HP H8. unfold nxb_frame. rewrite !cells_size_app, (sz_low11 _ _ _ _ _ _ _ _ _ _ _ H8). destruct HP as [-> | ->]; reflexivity.
Qed.
Lemma nxb_saved : forall (m : mem) A pd c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 g1 g2 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 r,
  (pd = 0 \/ pd = 16) -> c8s [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ->
  rw_cells asegs m A (nxb_frame pd c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 g1 g2 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 r) ->
  rw_cells asegs m (A + 176 + pd) [C8 e0; C8 r].
Proof.
  intros until r. intros HP H8 H. unfold nxb_frame in H.
  change [C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 r]
    with ([C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1] ++ [C8 e0; C8 r]) in H.
  rewrite !app_assoc in H. pose proof (rw_cells_skip m A _ _ H) as K.
  rewrite !cells_size_app, (sz_low11 _ _ _ _ _ _ _ _ _ _ _ H8) in K.
  replace (A + 176 + pd) with (A + Z.of_nat (88 + cells_size (if pd =? 0 then [] else [CB 8 g1; CB 8 g2])
                                              + cells_size [C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1]));
    [exact K|]. destruct HP as [-> | ->]; cbn; lia.
Qed.
Lemma nxb_blob : forall (m : mem) A pd c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 g1 g2 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 r,
  (pd = 0 \/ pd = 16) -> c8s [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ->
  rw_cells asegs m A (nxb_frame pd c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 g1 g2 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 r) ->
  exists lowj, rw_cells asegs m A [CB (Z.to_nat (88 + pd)) lowj; C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 r].
Proof.
  intros until r. intros HP H8 H. unfold nxb_frame in H. rewrite app_assoc in H. eexists.
  pose proof (rw_cells_merge asegs m A [] _ _ H) as K. cbn [app] in K.
  replace (Z.to_nat (88 + pd)) with (cells_size ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ (if pd =? 0 then [] else [CB 8 g1; CB 8 g2]))); [exact K|].
  rewrite cells_size_app, (sz_low11 _ _ _ _ _ _ _ _ _ _ _ H8). destruct HP as [-> | ->]; reflexivity.
Qed.
Lemma nxb_slot7 : forall (m : mem) A pd c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 g1 g2 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 r,
  c8s [c0; c1; c2; c3; c4; c5; c6] ->
  rw_cells asegs m A (nxb_frame pd c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 g1 g2 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 r) ->
  rw_cells asegs m (A + 56) [c7].
Proof.
  intros until r. intros H8 H. unfold nxb_frame in H.
  assert (K : rw_cells asegs m A ([c0; c1; c2; c3; c4; c5; c6] ++ c7 :: [c8; c9; c10] ++ (if pd =? 0 then [] else [CB 8 g1; CB 8 g2])
                                  ++ [C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 r])) by exact H.
  apply rw_cells_skip, rw_cells_head in K. unfold c8s in H8.
  repeat (apply Forall_cons_iff in H8; let E := fresh "E" in destruct H8 as [E H8]).
  replace (A + 56) with (A + Z.of_nat (cells_size [c0; c1; c2; c3; c4; c5; c6])) by (cbn [cells_size]; lia). exact K.
Qed.
(* [comment removed for export] *)
Ltac frb_keep H AG WM H' HP HB :=
  lazymatch type of H with
  | rw_cells _ ?m ?a ?cs =>
      lazymatch type of WM with wmono _ m ?m' =>
        assert (H' : rw_cells asegs m' a cs)
          by (apply (rw_cells_agree asegs m m' a cs H); [apply AG; [apply Z.le_refl | rewrite sz_nxb by first [exact HP | (unfold c8s; repeat constructor)]; exact HB] | exact WM]) end
  end.

Section CExd.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM2 : stack_malloc_contract RT 2.
Hypothesis C_FRN : crypto_free_null_env_stmt RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
(* [comment removed for export] *)
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m 0xba3e98 [C8 (Z_to_bv 64 0xbc5298)].
(* [comment removed for export] *)
Hypothesis GO_DC : GOBJ DC_CTX 328.
Hypothesis GO_DCKEY : GOBJ DC_KEY 4.

Definition NEWEX_STACK : Z := 320.
Definition NX_SITES : list (Z * Z) := [(SITE_nx_free, e_new_ex_data)].
Definition NX_CALLS : list (Z * Z) := [(SITE_nx_free, e_CRYPTO_free); (SITE_nx_free, e_free)].
(* [comment removed for export] *)
Definition NX_W (AD LK : Z) : list (Z * Z) := [(AD, AD + 16); (LK + 4, LK + 8)].

(* [comment removed for export] *)
Definition T_newex_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (kd LK AD p n : Z) (aw0 aw1 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 12 -> a2 = Z_to_bv 64 AD ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + NEWEX_STACK <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_new_ex_data (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) NX_SITES NX_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  exd_stat m kd LK -> In (LK, 40) (rt_live RT Σ) -> rw_cells asegs m LK (mutex_cells z64 z64) ->
  rw_cells asegs m AD [C8 aw0; C8 aw1] -> AD mod 8 = 0 -> In (p, n) (rt_live RT Σ) -> p mod 8 = 0 -> p <= AD -> AD + 16 <= p + n -> n <= 64512 -> p <> LK ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_new_ex_data m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (NX_W AD LK) m m'
           /\ cl_env m' lb canary /\ exd_stat m' kd LK
           /\ rw_cells asegs m' AD [C8 z64; C8 z64] /\ rw_cells asegs m' LK (mutex_cells z64 z64)) c
       /\ rts_same RT Σ Σ' 1).

Theorem T_newex_cps : T_newex_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary kd LK AD p n aw0 aw1
    FDO MST -> -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hcr EST INLK LKC ADC ADAL INP PAL PAD ADN NSM PNE CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA). unfold NEWEX_STACK in HSTK.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pd := usp mod 32).
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pd) by reflexivity. clearbody pd.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 320 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  assert (HLO : lo <= usp - 320) by (unfold RT_STACK in HSTK; lia).
  set (usp1 := usp + -192 - pd).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (FRB : usp1 + (192 + pd) <= USTACK_TOP) by (unfold usp1, USTACK_TOP in *; clear - NUM; lia).
  pose proof EST as (DCI & DCK & KD & O1 & R1 & O2 & R2 & TK & GL & LKAL & IPC).
  assert (DCKEY8 : DC_KEY mod 8 = 0) by reflexivity. assert (DCGL8 : DC_GLOBAL_LOCK mod 8 = 0) by reflexivity. assert (DCIP8 : DC_IP12 mod 8 = 0) by reflexivity.
  (* [comment removed for export] *)
  pose proof (af_live_range RT AF Σ m LK 40 ART0 INLK) as RLK. pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 INLK ltac:(lia)) as LKHI.
  pose proof (af_live_range RT AF Σ m p n ART0 INP) as RP. pose proof (afp_live_hi RT GOBJ AFP Σ m p n ART0 INP NSM) as PHI.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INP INLK ltac:(intros X; injection X as E1 E2; exact (PNE E1))) as DPL.
  (* [comment removed for export] *)
  assert (STA : forall a, client_static a -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside (NX_W AD LK) a /\ a < usp - 320).
  { intros a Ha. pose proof (client_static_range a Ha) as Ra. split; [right; left; exact Ha|]. unfold NX_W. cbn [outside]. unfold SEGTOP_A in *. clear - Ra PHI LKHI PAD HLOI HLO. lia. }
  (* [comment removed for export] *)
  pose proof (nx_w_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 12) a1 (Z_to_bv 64 AD) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(lia) ltac:(fold usp; lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) MI0) as WW.
  cl_lift WW HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  destruct (af_client_consts RT AF Σ m1 ART1) as (_ & SHC1 & _ & UAR1 & UT1).
  (* [comment removed for export] *)
  pose proof (nx_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 12) a1 (Z_to_bv 64 AD) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo pd
                HP HPM ST1 ltac:(fold usp; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT1 SHC1 UAR1 MI1) as W0.
  cl_lift W0 Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (a1' & a2' & j0 & j1 & j2 & j3 & j4 & j5 & j6 & j8 & j9 & j10 & g1 & g2 & m2 & -> & MU2 & WM2 & MI2 & FR2 & ST2) & Hc2'). clear Hc2.
  fold usp in MU2, FR2, ST2, Hc2'. fold usp1 in FR2, ST2, Hc2'.
  pose proof (cl_seg_ART RT AF Σ m1 m2 usp 208 [] ART1 ltac:(lia) ltac:(lia) MU2 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM2) as ART2.
  assert (A02 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 320 \/ usp <= bv_unsigned x -> m2 x = m x).
  { intros x Hx Hlt. rewrite (MU2 x ltac:(cbn [outside]; clear - Hlt; lia)). apply MU1. cbn [outside]. clear - Hlt. lia. }
  (* [comment removed for export] *)
  apply (SM2 Σ PMc (Z_to_bv 64 SITE_nx_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 160) a1' a2' (Z_to_bv 64 AD) a4 a5 a6 a7
           s2 (Z_to_bv 64 AD) (Z_to_bv 64 12) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo FDO MST ltac:(right; right; reflexivity) eq_refl Hfr Hcr ART2 MI2).
  { fold usp in SPA. unfold call_ok. rewrite EU1. split; [exact ST2|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc2'. }
  clear Hc2'. intros c3 (Σ1 & f & Hc3 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & WF3 & WS3) & Hc3'). clear Hc3.
  destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite (ret_pc_even SITE_nx_smalloc) in Hc3' by (unfold SITE_nx_smalloc; lia).
  assert (INF : In (f, 2%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m3 f 2%nat ART3 INF) as (_ & FLO & _ & PF).
  assert (INP1 : In (p, n) (rt_live RT Σ1)) by (rewrite LV1; exact INP). assert (INLK1 : In (LK, 40) (rt_live RT Σ1)) by (rewrite LV1; exact INLK).
  pose proof (PF p n INP1) as PFP. pose proof (PF LK 40 INLK1) as PFL. clear PF.
  pose proof (proj1 (af_fshadow_apart RT AF Σ1 m3 f 2%nat ART3 INF) p n INP1) as SFP.
  pose proof (proj1 (af_fshadow_apart RT AF Σ1 m3 f 2%nat ART3 INF) LK 40 INLK1) as SFL.
  change (fs_size 2) with 256 in PFP, PFL, SFP, SFL.
  pose proof (af_frames_align RT AF Σ1 m3 f 2%nat ART3 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m3 f 2%nat ART3 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 2) with 256 in FLO, FSH, FU, WF3, WS3. change (256 - 8) with 248 in WF3. change (256 / 8) with 32 in WS3.
  unfold shad, SHB in WS3. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 256) = shad f + 32) by (replace (f + 256) with (f + 64 * 4) by lia; rewrite (shad_add64 f 4 F64); lia).
  rewrite SHF in SFP, SFL. unfold shad, SHB in SFP, SFL.
  pose proof (div8_facts f) as Q1.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(clear - F0; lia) ltac:(clear; lia)) as DP. assert (D44 : f / 8 + 32 <= 2^44) by (clear - FU F0; unfold USTACK_TOP in FU; Z.div_mod_to_equations; lia).
    clear - DP D44. lia. }
  assert (AG3 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES3. left. lia. }
  frb_keep FR2 AG3 WM3 FR3 HP FRB.
  destruct (wr_at_rw_CB m3 f 248 WF3 ltac:(lia)) as (fj & FB3). destruct (wr_at_rw_CB m3 (f / 8 + 2147450880) 32 WS3 ltac:(lia)) as (sj & SB3).
  change (Z.to_nat 248) with 248%nat in FB3. change (Z.to_nat 32) with 32%nat in SB3.
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & SHC3 & _ & _ & UT3).
  (* [comment removed for export] *)
  pose proof (nx_s1_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s7 s8 s9 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 F3 fc3 m3 0 12 AD f lo pd j0 j1 j2 j3 j4 j5 j6 j8 j9 j10 g1 g2 fj sj
                HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                ltac:(lia) ltac:(lia) ltac:(clear - PHI PAD ADN RP SP0R; unfold USTACK_TOP, STACK_WIN, SEGTOP_A in *; lia) UT3 FR3 ST3 FB3 SB3 MI3) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (jf & sjr & m4 & -> & MU4 & WM4 & MI4 & FR4 & ST4 & FB4 & SB4) & Hc4'). clear Hc4.
  fold usp in MU4, FR4, ST4, Hc4'. fold usp1 in MU4, FR4, ST4, Hc4'.
  pose proof (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 WM4))) as WM04.
  assert (ART4 : ART RT Σ1 m4).
  { apply (af_frame RT AF Σ1 m3 m4 usp1 ART3 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM4].
    intros a Ha. apply MU4. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply acl_stack. unfold usp1, USTACK_TOP in *. lia.
    - apply (acl_frame _ _ _ f 2%nat); [exact INF | change (fs_size 2) with 256; lia].
    - apply (acl_fshadow _ _ _ f 2%nat); [exact INF | rewrite SHF; unfold shad, SHB; lia]. }
  destruct (af_client_consts RT AF Σ1 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  (* [comment removed for export] *)
  assert (G4 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 320 \/ usp <= bv_unsigned x -> m4 x = m x).
  { intros x Hx Hlt.
    destruct (newframe_apart RT AF Σ Σ1 m3 f 2%nat usp _ ART3 FRS1 LV1 SP1 ltac:(lia) Hx) as (N1 & N2).
    change (fs_size 2) with 256 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU4 x ltac:(cbn [outside]; unfold usp1; clear - N1 N2 Hlt HP; lia)).
    rewrite (PRES3 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia])).
    exact (A02 x Hx Hlt). }
  assert (EST4 : exd_stat m4 kd LK).
  { apply (exd_stat_agree m m4 kd LK EST). intros x Hx. destruct (STA _ (exd_fp_static kd _ KD Hx)) as (Hc & _ & Hl). exact (G4 x Hc ltac:(left; exact Hl)). }
  pose proof EST4 as (DCI4 & DCK4 & _ & O14 & R14 & O24 & R24 & TK4 & _ & _ & _).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m4 DC_KEY 4 DC_KEY ART4 GO_DCKEY ltac:(lia) ltac:(lia) DCKEY8) as DCKS4.
  replace (if DC_KEY + 4 - DC_KEY <? 8 then DC_KEY + 4 - DC_KEY else 0) with 4 in DCKS4 by reflexivity.
  assert (TC4 : ro_cells asegs m4 (bv_unsigned (Z_to_bv 64 0xba3ef0) + -88) [C8 (Z_to_bv 64 0xbc5298)]).
  { replace (bv_unsigned (Z_to_bv 64 0xba3ef0) + -88) with 0xba3e98 by (rewrite unsigned_lit by lia; reflexivity). exact (proj1 (TSD _ _ ART4)). }
  (* [comment removed for export] *)
  pose proof (nx_s2a_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b3 b4 b5 b6 b7 s8 s9 s10 u3 u4 u5 u6 F3 fc3 m4 12 AD f lo pd 0xbc5298 kd 4
                HP ltac:(fold usp; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) DCI4 DCK4 ltac:(lia) DCKS4 ltac:(right; reflexivity) UT4 SHC4 O14 R14 O24 R24
                TC4 ltac:(rewrite unsigned_lit by lia; lia) ltac:(rewrite unsigned_lit by lia; unfold SEGTOP_A in HLOI; lia) ltac:(lia) TK4 ltac:(unfold SEGTOP_A in HLOI; lia) ST4 MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (v1 & d1 & d2 & d3 & m5 & -> & MU5 & WM5 & MI5 & ST5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, Hc5'. fold usp1 in MU5, ST5, Hc5'.
  pose proof (wmono_trans asegs _ _ _ WM04 WM5) as WM05.
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 (usp1 - 48) ART4 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply acl_stack. unfold usp1, USTACK_TOP in *. lia. }
  assert (G5 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 320 \/ usp <= bv_unsigned x -> m5 x = m x).
  { intros x Hx Hlt. rewrite (MU5 x ltac:(cbn [outside]; unfold usp1; clear - Hlt HP; lia)). exact (G4 x Hx Hlt). }
  (* [comment removed for export] *)
  assert (EST5 : exd_stat m5 kd LK).
  { apply (exd_stat_agree m m5 kd LK EST). intros x Hx. destruct (STA _ (exd_fp_static kd _ KD Hx)) as (Hc & _ & Hl). exact (G5 x Hc ltac:(left; exact Hl)). }
  pose proof EST5 as (_ & _ & _ & _ & _ & _ & _ & _ & GL5 & _ & IPC5).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m5 DC_CTX 328 DC_GLOBAL_LOCK ART5 GO_DC ltac:(unfold DC_GLOBAL_LOCK; lia) ltac:(unfold DC_GLOBAL_LOCK; lia) DCGL8) as GLS5.
  replace (if DC_CTX + 328 - DC_GLOBAL_LOCK <? 8 then DC_CTX + 328 - DC_GLOBAL_LOCK else 0) with 0 in GLS5 by reflexivity.
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m5 DC_CTX 328 DC_IP12 ART5 GO_DC ltac:(unfold DC_IP12; lia) ltac:(unfold DC_IP12; lia) DCIP8) as IPS5.
  replace (if DC_CTX + 328 - DC_IP12 <? 8 then DC_CTX + 328 - DC_IP12 else 0) with 0 in IPS5 by reflexivity.
  assert (LKC5 : rw_cells asegs m5 LK (mutex_cells z64 z64)).
  { apply (rw_cells_agree asegs m m5 _ _ LKC); [| exact WM05]. intros x Hx. cbv beta in Hx. cbn [cells_size mutex_cells csize Nat.add] in Hx.
    apply G5; [apply (acl_live _ _ _ LK 40); [exact INLK | lia] | left; clear - Hx RLK NUM; lia]. }
  assert (ADC5 : rw_cells asegs m5 AD [C8 aw0; C8 aw1]).
  { apply (rw_cells_agree asegs m m5 _ _ ADC); [| exact WM05]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply G5; [apply (acl_live _ _ _ p n); [exact INP | lia] | left; clear - Hx RP PAD ADN NUM; lia]. }
  pose proof (proj2 (af_acc_live RT AF Σ1 m5 p n ART5 INP1)) as ACC5.
  pose proof (acc_shadow0 m5 p n AD ACC5 PAL ltac:(lia) PAD ltac:(clear - PAD ADN; Z.div_mod_to_equations; lia)) as ADS15.
  pose proof (acc_shadow0 m5 p n (AD + 8) ACC5 PAL ltac:(lia) ltac:(lia) ltac:(clear - PAD ADN; Z.div_mod_to_equations; lia)) as ADS25.
  destruct (af_client_consts RT AF Σ1 m5 ART5) as (_ & SHC5 & _ & _ & UT5).
  assert (AG5 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m4 m5).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply MU5. cbn [outside]. clear - Hx H1. lia. }
  frb_keep FR4 AG5 WM5 FR5 HP FRB.
  (* [comment removed for export] *)
  pose proof (nx_s2_walk sp gp (Z_to_bv 64 0xba3ef0) u0 v1 u2 d1 d2 d3 b4 b5 b6 b7 s8 s9 s10 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 aw0 aw1 F3 fc3 m5 12 AD LK f lo pd j0 j1 j2 j3 j4 j5 j6 j8 j9 g1 g2
                HP F0 F64 FIMG ltac:(clear - FLO LOW; lia) ltac:(clear - FSH; destruct FSH; [left | right]; lia) ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia)
                ltac:(fold usp; clear - NUM; unfold USTACK_TOP in *; lia) eq_refl
                UT5 SHC5 GL5 LKHI LKAL ltac:(clear - RLK LOW; lia) LKC5 GLS5 IPC5 IPS5 ADC5 ltac:(clear - PHI PAD; lia) ADAL ltac:(clear - RP LOW ADN; lia)
                ltac:(clear - DPL PAD ADN; lia) ltac:(right; clear - PHI PAD; lia) ADS15 ADS25
                FR5 ST5 MI5) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (w0 & w1 & w2 & g3 & g4 & g5 & g6 & g7 & m6 & -> & MU6 & WM6 & MI6 & FR6 & ST6 & ADC6 & LKC6) & Hc6'). clear Hc6.
  fold usp in MU6, FR6, ST6, Hc6'. fold usp1 in FR6, ST6, Hc6'.
  pose proof (wmono_trans asegs _ _ _ WM05 WM6) as WM06.
  assert (ART6 : ART RT Σ1 m6).
  { apply (af_frame RT AF Σ1 m5 m6 (usp - 320) ART5 ltac:(rewrite SP1; lia)); [| exact WM6].
    intros a Ha. apply MU6. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply acl_stack. unfold USTACK_TOP in *. lia.
    - apply (acl_live _ _ _ p n); [exact INP1 | lia].
    - apply (acl_live _ _ _ LK 40); [exact INLK1 | lia]. }
  assert (B6 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (NX_W AD LK) (bv_unsigned x) -> m6 x = m x).
  { intros x Hx Ho. unfold NX_W in Ho. cbn [outside] in Ho. destruct (cl_split RT AF Σ m usp 320 _ ART0 ltac:(lia) ltac:(lia) Hx) as [Hi|Lo].
    - rewrite (MU6 x ltac:(cbn [outside]; clear - Hi Ho; lia)). exact (G5 x Hx ltac:(right; exact Hi)).
    - rewrite (MU6 x ltac:(cbn [outside]; clear - Lo Ho; lia)). exact (G5 x Hx ltac:(left; exact Lo)). }
  assert (AG06 : agree_on (fun x => usp <= x < USTACK_TOP) m m6).
  { intros x Hx. cbv beta in Hx. apply B6; [apply acl_stack; exact Hx|]. unfold NX_W. cbn [outside]. clear - Hx RP RLK NUM PAD ADN. lia. }
  assert (CLE6 : cl_env m6 lb canary).
  { apply (cl_env_agree m m6 _ _ CLE). intros x Hx. destruct (STA _ (cl_cell_static _ Hx)) as (Hc & Ho & _). exact (B6 x Hc Ho). }
  pose proof FR6 as SV6. apply nxb_saved in SV6; [| exact HP | unfold c8s; repeat constructor].
  replace (usp1 + 176 + pd) with (usp - 16) in SV6 by (unfold usp1; clear; lia).
  destruct (cl_chain_call (rt_cg RT Σ) e_new_ex_data e_CRYPTO_free SITE_nx_free m m6 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG06
              ltac:(fold usp; exact SV6)
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX6 & UWC6).
  rewrite <- CG1 in CTX6.
  (* [comment removed for export] *)
  apply (C_FRN Σ1 PMc (Z_to_bv 64 SITE_nx_free) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 0) (Z_to_bv 64 EXD_FILE) (Z_to_bv 64 259)
           g3 g4 g5 g6 g7 (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 SHB) (Z_to_bv 64 f) (Z_to_bv 64 DC_IP12)
           (Z_to_bv 64 (f + 32)) (Z_to_bv 64 DC_GLOBAL_LOCK) (Z_to_bv 64 (f / 8 + 2147450880)) u3 u4 u5 u6 F3 fc3 m6 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ART6 MI6).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST6|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK HP; lia|].
    split; [unfold USTACK_TOP in *; clear - NUM HP; lia|]. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { rewrite (unsigned_lit SITE_nx_free) by (unfold SITE_nx_free; lia). exact CTX6. }
  { exact UWC6. }
  { rewrite CG1. rewrite (unsigned_lit SITE_nx_free) by (unfold SITE_nx_free; lia). apply (proj2 CGH). right; left; reflexivity. }
  { exact CLE6. }
  { exact Hc6'. }
  clear Hc6'. intros c7 (v & Hc7).
  destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & CLE7) & Hc7'). clear Hc7.
  destruct RS7 as (x0 & x1 & x2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & x3 & x4 & x5 & x6 & F7 & fc7 & ->).
  rewrite EU1 in ST7, PRES7. rewrite (ret_pc_even SITE_nx_free) in Hc7' by (unfold SITE_nx_free; lia).
  pose proof (wmono_trans asegs _ _ _ WM06 WM7) as WM07. pose proof (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 WM7)) as WM47.
  (* [comment removed for export] *)
  assert (AG7 : forall a k, (usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 248) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 32) ->
            agree_on (fun x => a <= x < a + k) m6 m7).
  { intros a k H x Hx. cbv beta in Hx. apply PRES7. destruct H as [H|[H|H]].
    - left. clear - H Hx. lia.
    - apply (acl_frame _ _ _ f 2%nat); [exact INF | change (fs_size 2) with 256; clear - H Hx; lia].
    - apply (acl_fshadow _ _ _ f 2%nat); [exact INF | rewrite SHF; unfold shad, SHB; clear - H Hx; lia]. }
  assert (AG7s : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m6 m7) by (intros a k H1 H2; apply AG7; left; split; assumption).
  frb_keep FR6 AG7s WM7 FR7 HP FRB.
  (* [comment removed for export] *)
  assert (K47 : forall x : word, (f <= bv_unsigned x < f + 248) \/ (f / 8 + 2147450880 <= bv_unsigned x < f / 8 + 2147450880 + 32) -> m7 x = m4 x).
  { intros x Hx.
    assert (E7 : m7 x = m6 x).
    { destruct Hx as [Hx|Hx]; [exact (AG7 f 248 ltac:(right; left; clear; lia) x Hx) | exact (AG7 (f / 8 + 2147450880) 32 ltac:(right; right; clear; lia) x Hx)]. }
    rewrite E7. rewrite (MU6 x ltac:(cbn [outside]; clear - Hx PFP PFL SFP SFL PAD ADN FLO NUM SHR HLO; lia)).
    apply MU5. cbn [outside]. unfold usp1. clear - Hx FLO NUM SHR HLO HP. lia. }
  destruct (rw_cells_forget asegs m4 f _ (rw_cells_head m4 f _ _ FB4)) as (hj & HDR4). cbn [cells_size csize Nat.add] in HDR4.
  assert (HDR7 : rw_cells asegs m7 f [CB 8 hj]).
  { apply (rw_cells_agree asegs m4 m7 _ _ HDR4); [| exact WM47]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply K47. left. clear - Hx. lia. }
  destruct (rw_cells_forget asegs m4 _ _ SB4) as (sj' & SB4'). unfold nx_shadow_live in SB4'. cbn [cells_size csize Nat.add map app] in SB4'.
  assert (SB7 : rw_cells asegs m7 (f / 8 + 2147450880) [CB 32 sj']).
  { apply (rw_cells_agree asegs m4 m7 _ _ SB4'); [| exact WM47]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply K47. right. clear - Hx. lia. }
  (* [comment removed for export] *)
  pose proof (nx_x1_walk (Z_to_bv 64 SITE_nx_free) sp gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 v h1 h2 h3 h4 h5 h6 h7 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-1))
                (Z_to_bv 64 SHB) (Z_to_bv 64 f) (Z_to_bv 64 DC_IP12) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 DC_GLOBAL_LOCK) x3 x4 x5 x6
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra (Z_to_bv 64 (f + 32)) a1 (Z_to_bv 64 f)
                F7 fc7 m7 f lo pd hj sj' j0 j1 j2 j3 j4 j8 j9 g1 g2
                HP ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)
                F0 FIMG ltac:(clear - FLO LOW; lia) ltac:(clear - FSH; destruct FSH; [left | right]; lia) ST7 FR7 HDR7 SB7 MI7) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc7' c8 Hc8.
  destruct (ASTA_unpack RT Σ1 _ _ c8 Hc8) as (ms8 & (ra1 & m8 & -> & MU8 & WM8 & MI8 & HDR8 & SB8) & Hc8'). clear Hc8.
  fold usp in Hc8'. fold usp1 in Hc8'.
  assert (ART8 : ART RT Σ1 m8).
  { apply (af_frame RT AF Σ1 m7 m8 usp1 ART7 ltac:(rewrite SP1; unfold usp1; clear - NUM HP; lia)); [| exact WM8].
    intros a Ha. apply MU8. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 2%nat); [exact INF | change (fs_size 2) with 256; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ f 2%nat); [exact INF | rewrite SHF; unfold shad, SHB; clear - Hin; lia]. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ1 m8 f 2%nat (rt_frames RT Σ) ART8 FRS1) as (Σ2 & flg & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 2) with 256 in FW. replace (f + 256 - 8) with (f + 248) in FW by lia. rewrite SP1 in FLW.
  assert (FLLO : flg + 1 <= lo) by (clear - FLW LOW; lia).
  assert (AG8 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply MU8. cbn [outside]. unfold usp1 in H1. clear - Hx H1 FLO NUM SHR HLO HP. lia. }
  frb_keep FR7 AG8 WM8 FR8 HP FRB.
  pose proof FR8 as FR8b. apply nxb_blob in FR8b; [| exact HP | unfold c8s; repeat constructor]. destruct FR8b as (lowj & FR8b).
  assert (ST8 : stk asegs m8 lo usp1).
  { apply (stk_agree_nw asegs m7 m8 _ _ ST7). intros x Hx. cbv beta in Hx. unfold usp1 in Hx. apply MU8. cbn [outside]. clear - Hx FLO LOW NUM SHR HP. lia. }
  (* [comment removed for export] *)
  pose proof (nx_x2_walk ra1 ra sp gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 (Z_to_bv 64 (-11)) h1 h2 h3 h4 h5 h6 h7 (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-1))
                (Z_to_bv 64 SHB) (Z_to_bv 64 DC_IP12) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 DC_GLOBAL_LOCK) (Z_to_bv 64 (f / 8 + 2147450880)) x3 x4 x5 x6
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F7 fc7 m8 f flg lo pd lowj
                HP ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)
                F0 ltac:(clear - FLO LOW; lia) FL0 FLLO ST8 FR8b FW FLC MI8) as W5.
  fold usp usp1 in W5.
  cl_lift W5 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ1 _ _ c9 Hc9) as (ms9 & (y0 & y1 & y2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & y3 & y4 & y5 & y6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & FLC9) & Hc9'). clear Hc9.
  fold usp in ST9.
  destruct (REL m9 MU9 WM9 FLC9) as (ART9 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).
  (* [comment removed for export] *)
  assert (NFL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> x <> flg).
  { intros x Hx Ex. subst x. destruct Hx as [H|H]; [unfold USTACK_TOP, RT_STACK, STACK_WIN in *; clear - H FLW NUM; lia|].
    apply NAC. right. rewrite LV1, FRS1.
    destruct H as [H|[H|[H|H]]]; [left; exact H | right; left; exact H
      | right; right; left; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]
      | right; right; right; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]]. }
  (* [comment removed for export] *)
  assert (A79 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m9 x = m7 x).
  { intros x Hx.
    destruct (newframe_apart RT AF Σ Σ1 m3 f 2%nat usp _ ART3 FRS1 LV1 SP1 ltac:(clear - NUM; lia) Hx) as (N1 & N2).
    change (fs_size 2) with 256 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU9 x ltac:(cbn [outside]; split; [pose proof (NFL _ Hx); lia | exact I])).
    apply MU8. cbn [outside]. clear - N1 N2. lia. }
  assert (P7 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m7 x = m6 x).
  { intros x Hx. apply PRES7. rewrite LV1, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | intros e He; right; exact He | unfold usp1; clear - HP; lia]. }
  assert (B9 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (NX_W AD LK) (bv_unsigned x) -> m9 x = m x).
  { intros x Hx Ho. rewrite (A79 x Hx), (P7 x Hx). exact (B6 x Hx Ho). }
  apply Hk. exists Σ2.
  split; [| unfold rts_same; rewrite LV3, LV1, FRS3, SP3, SP1, CR3, CR1, CG3, CG1; repeat split; first [reflexivity | lia]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ1 Σ2 PMc _ c9 Hc9' AL3 AM3)|]. intros ms <-. exists m9.
  split; [exists y0, y1, y2, i1, i2, i3, i4, i5, i6, i7, y3, y4, y5, y6, F7, fc7; reflexivity|].
  split; [split; [exact ART9 | split; [exact MI9 | split; [exact (wmono_trans asegs _ _ _ WM07 (wmono_trans asegs _ _ _ WM8 WM9)) | exact ST9]]]|].
  split; [exact B9|].
  split; [| split; [| split]].
  - apply (cl_env_agree m7 m9 _ _ CLE7). intros x Hx. apply A79. exact (proj1 (STA _ (cl_cell_static _ Hx))).
  - apply (exd_stat_agree m m9 kd LK EST). intros x Hx. destruct (STA _ (exd_fp_static kd _ KD Hx)) as (Hc & Ho & _). exact (B9 x Hc Ho).
  - apply (rw_cells_agree_nw asegs m6 m9 _ _ ADC6). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    assert (Hc : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)) by (apply (acl_live _ _ _ p n); [exact INP | clear - Hx PAD ADN; lia]).
    rewrite (A79 x Hc). exact (P7 x Hc).
  - apply (rw_cells_agree_nw asegs m6 m9 _ _ LKC6). intros x Hx. cbv beta in Hx. cbn [cells_size mutex_cells csize Nat.add] in Hx.
    assert (Hc : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)) by (apply (acl_live _ _ _ LK 40); [exact INLK | clear - Hx; lia]).
    rewrite (A79 x Hc). exact (P7 x Hc).
Qed.
(* [comment removed for export] *)
Definition FREEEX_STACK : Z := 320.
Definition FX_SITES : list (Z * Z) := [(SITE_fx_free, e_free_ex_data_A)].
Definition FX_CALLS : list (Z * Z) := [(SITE_fx_free, e_CRYPTO_free); (SITE_fx_free, e_free)].

(* [comment removed for export] *)
Definition T_freeex_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (kd LK AD p n : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 12 -> a2 = Z_to_bv 64 AD ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + FREEEX_STACK <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_free_ex_data_A (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) FX_SITES FX_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  exd_stat m kd LK -> In (LK, 40) (rt_live RT Σ) -> rw_cells asegs m LK (mutex_cells z64 z64) ->
  rw_cells asegs m AD [C8 z64; C8 z64] -> AD mod 8 = 0 -> In (p, n) (rt_live RT Σ) -> p mod 8 = 0 -> p <= AD -> AD + 16 <= p + n -> n <= 64512 -> p <> LK ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free_ex_data_A m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (v : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (NX_W AD LK) m m'
           /\ cl_env m' lb canary /\ exd_stat m' kd LK
           /\ rw_cells asegs m' AD [C8 z64; C8 z64] /\ rw_cells asegs m' LK (mutex_cells z64 z64)) c
       /\ rts_same RT Σ Σ' 1).

Theorem T_freeex_cps : T_freeex_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary kd LK AD p n
    FDO MST -> -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hcr EST INLK LKC ADC ADAL INP PAL PAD ADN NSM PNE CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA). unfold FREEEX_STACK in HSTK.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pd := usp mod 32).
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pd) by reflexivity. clearbody pd.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 352 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  assert (HLO : lo <= usp - 352) by (unfold RT_STACK in HSTK; lia).
  set (usp1 := usp + -192 - pd).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (FRB : usp1 + (192 + pd) <= USTACK_TOP) by (unfold usp1, USTACK_TOP in *; clear - NUM; lia).
  pose proof EST as (DCI & DCK & KD & O1 & R1 & O2 & R2 & TK & GL & LKAL & IPC).
  assert (DCKEY8 : DC_KEY mod 8 = 0) by reflexivity. assert (DCGL8 : DC_GLOBAL_LOCK mod 8 = 0) by reflexivity. assert (DCIP8 : DC_IP12 mod 8 = 0) by reflexivity.
  pose proof (af_live_range RT AF Σ m LK 40 ART0 INLK) as RLK. pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 INLK ltac:(lia)) as LKHI.
  pose proof (af_live_range RT AF Σ m p n ART0 INP) as RP. pose proof (afp_live_hi RT GOBJ AFP Σ m p n ART0 INP NSM) as PHI.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INP INLK ltac:(intros X; injection X as E1 E2; exact (PNE E1))) as DPL.
  assert (STA : forall a, client_static a -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside (NX_W AD LK) a /\ a < usp - 352).
  { intros a Ha. pose proof (client_static_range a Ha) as Ra. split; [right; left; exact Ha|]. unfold NX_W. cbn [outside]. unfold SEGTOP_A in *. clear - Ra PHI LKHI PAD HLOI HLO. lia. }
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC0 & _ & UAR0 & UT0).
  (* [comment removed for export] *)
  pose proof (fx_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 12) a1 (Z_to_bv 64 AD) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd
                HP HPM ST ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) UT0 SHC0 UAR0 MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j0 & j1 & j2 & j3 & j4 & j6 & j8 & j9 & j10 & g1 & g2 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 208 [] ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (A01 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 352 \/ usp <= bv_unsigned x -> m1 x = m x).
  { intros x Hx Hlt. apply MU1. cbn [outside]. clear - Hlt. lia. }
  (* [comment removed for export] *)
  apply (SM2 Σ PMc (Z_to_bv 64 SITE_fx_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 256) a1' a2' a3 (Z_to_bv 64 0x7fff8000) a5 a6 a7
           s2 s3 (Z_to_bv 64 AD) (Z_to_bv 64 12) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(right; right; reflexivity) eq_refl Hfr Hcr ART1 MI1).
  { fold usp in SPA. unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK HP; lia|]. split; [unfold USTACK_TOP in *; clear - NUM HP; lia|].
    clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_fx_smalloc) in Hc2' by (unfold SITE_fx_smalloc; lia).
  assert (INF : In (f, 2%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 2%nat ART2 INF) as (_ & FLO & _ & PF).
  assert (INP1 : In (p, n) (rt_live RT Σ1)) by (rewrite LV1; exact INP). assert (INLK1 : In (LK, 40) (rt_live RT Σ1)) by (rewrite LV1; exact INLK).
  pose proof (PF p n INP1) as PFP. pose proof (PF LK 40 INLK1) as PFL. clear PF.
  pose proof (proj1 (af_fshadow_apart RT AF Σ1 m2 f 2%nat ART2 INF) p n INP1) as SFP.
  pose proof (proj1 (af_fshadow_apart RT AF Σ1 m2 f 2%nat ART2 INF) LK 40 INLK1) as SFL.
  change (fs_size 2) with 256 in PFP, PFL, SFP, SFL.
  pose proof (af_frames_align RT AF Σ1 m2 f 2%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 2%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 2) with 256 in FLO, FSH, FU, WF2, WS2. change (256 - 8) with 248 in WF2. change (256 / 8) with 32 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 256) = shad f + 32) by (replace (f + 256) with (f + 64 * 4) by lia; rewrite (shad_add64 f 4 F64); lia).
  rewrite SHF in SFP, SFL. unfold shad, SHB in SFP, SFL.
  pose proof (div8_facts f) as Q1.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(clear - F0; lia) ltac:(clear; lia)) as DP. assert (D44 : f / 8 + 32 <= 2^44) by (clear - FU F0; unfold USTACK_TOP in FU; Z.div_mod_to_equations; lia).
    clear - DP D44. lia. }
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. clear - H1 H2 Hx. lia. }
  frb_keep FR1 AG2 WM2 FR2 HP FRB.
  destruct (wr_at_rw_CB m2 f 248 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 32 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 248) with 248%nat in FB2. change (Z.to_nat 32) with 32%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (G2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 352 \/ usp <= bv_unsigned x -> m2 x = m x).
  { intros x Hx Hlt. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear - HP; lia])). exact (A01 x Hx Hlt). }
  assert (ADC2 : rw_cells asegs m2 AD [C8 z64; C8 z64]).
  { apply (rw_cells_agree asegs m m2 _ _ ADC); [| exact (wmono_trans asegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply G2; [apply (acl_live _ _ _ p n); [exact INP | clear - Hx PAD ADN; lia] | left; clear - Hx RP PAD ADN NUM; lia]. }
  pose proof (proj2 (af_acc_live RT AF Σ1 m2 p n ART2 INP1)) as ACC2.
  pose proof (acc_shadow0 m2 p n AD ACC2 PAL ltac:(clear - PHI; lia) PAD ltac:(clear - PAD ADN; Z.div_mod_to_equations; lia)) as ADS12.
  (* [comment removed for export] *)
  pose proof (fx_s1_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 (Z_to_bv 64 0) F2 fc2 m2 12 AD f lo pd j0 j1 j2 j3 j4 j6 j8 j9 j10 g1 g2 fj sj
                HP F0 F64 FIMG ltac:(clear - FLO LOW; lia) ltac:(clear - FSH; destruct FSH; [left | right]; lia) ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia)
                ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) ltac:(clear; lia)
                ltac:(clear - PHI PAD; lia) ADAL ltac:(clear - RP LOW ADN; lia) ltac:(right; clear - PHI PAD; lia) ltac:(clear - PFP PAD ADN; lia) ADC2 ADS12
                UT2 FR2 ST2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (jf & m3 & -> & MU3 & WM3 & MI3 & FR3 & ST3 & FB3 & SB3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, ST3, Hc3'. fold usp1 in MU3, FR3, ST3, Hc3'.
  pose proof (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) as WM03.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; clear - NUM HP; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hin NUM HP. lia.
    - apply (acl_frame _ _ _ f 2%nat); [exact INF | change (fs_size 2) with 256; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ f 2%nat); [exact INF | rewrite SHF; unfold shad, SHB; clear - Hin; lia]. }
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & SHC3 & _ & _ & UT3).
  assert (G3 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 352 \/ usp <= bv_unsigned x -> m3 x = m x).
  { intros x Hx Hlt.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 2%nat usp _ ART2 FRS1 LV1 SP1 ltac:(clear - NUM; lia) Hx) as (N1 & N2).
    change (fs_size 2) with 256 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU3 x ltac:(cbn [outside]; unfold usp1; clear - N1 N2 Hlt HP; lia)). exact (G2 x Hx Hlt). }
  assert (EST3 : exd_stat m3 kd LK).
  { apply (exd_stat_agree m m3 kd LK EST). intros x Hx. destruct (STA _ (exd_fp_static kd _ KD Hx)) as (Hc & _ & Hl). exact (G3 x Hc ltac:(left; exact Hl)). }
  pose proof EST3 as (DCI3 & DCK3 & _ & O13 & R13 & O23 & R23 & TK3 & _ & _ & _).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m3 DC_KEY 4 DC_KEY ART3 GO_DCKEY ltac:(clear; lia) ltac:(clear; lia) DCKEY8) as DCKS3.
  replace (if DC_KEY + 4 - DC_KEY <? 8 then DC_KEY + 4 - DC_KEY else 0) with 4 in DCKS3 by reflexivity.
  assert (TC3 : ro_cells asegs m3 (bv_unsigned (Z_to_bv 64 0xba3ef0) + -88) [C8 (Z_to_bv 64 0xbc5298)]).
  { replace (bv_unsigned (Z_to_bv 64 0xba3ef0) + -88) with 0xba3e98 by (rewrite unsigned_lit by (clear; lia); reflexivity). exact (proj1 (TSD _ _ ART3)). }
  (* [comment removed for export] *)
  pose proof (fx_s2a_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 (Z_to_bv 64 (-13)) (Z_to_bv 64 FX_DESCR) (Z_to_bv 64 e_free_ex_data_A) (Z_to_bv 64 0x7fff8000) b5 b6 b7
                s2 s7 s8 s9 s10 u3 u4 u5 u6 F2 fc2 m3 12 AD f lo pd 0xbc5298 kd 4
                HP ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) DCI3 DCK3 ltac:(clear - KD; lia) DCKS3 ltac:(right; reflexivity)
                UT3 SHC3 O13 R13 O23 R23
                TC3 ltac:(rewrite unsigned_lit by (clear; lia); clear; lia) ltac:(rewrite unsigned_lit by (clear; lia); unfold SEGTOP_A in HLOI; clear - HLOI; lia) ltac:(clear; lia) TK3
                ltac:(unfold SEGTOP_A in HLOI; clear - HLOI KD; lia) ST3 MI3) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (v1 & d1 & d2 & d3 & m4 & -> & MU4 & WM4 & MI4 & ST4) & Hc4'). clear Hc4.
  fold usp in MU4, ST4, Hc4'. fold usp1 in MU4, ST4, Hc4'.
  pose proof (wmono_trans asegs _ _ _ WM03 WM4) as WM04.
  assert (ART4 : ART RT Σ1 m4).
  { apply (af_frame RT AF Σ1 m3 m4 (usp1 - 48) ART3 ltac:(rewrite SP1; unfold usp1; clear - NUM HP; lia)); [| exact WM4].
    intros a Ha. apply MU4. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hin NUM HP. lia. }
  assert (G4 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 352 \/ usp <= bv_unsigned x -> m4 x = m x).
  { intros x Hx Hlt. rewrite (MU4 x ltac:(cbn [outside]; unfold usp1; clear - Hlt HP; lia)). exact (G3 x Hx Hlt). }
  assert (EST4 : exd_stat m4 kd LK).
  { apply (exd_stat_agree m m4 kd LK EST). intros x Hx. destruct (STA _ (exd_fp_static kd _ KD Hx)) as (Hc & _ & Hl). exact (G4 x Hc ltac:(left; exact Hl)). }
  pose proof EST4 as (_ & _ & _ & _ & _ & _ & _ & _ & GL4 & _ & IPC4).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m4 DC_CTX 328 DC_GLOBAL_LOCK ART4 GO_DC ltac:(unfold DC_GLOBAL_LOCK; clear; lia) ltac:(unfold DC_GLOBAL_LOCK; clear; lia) DCGL8) as GLS4.
  replace (if DC_CTX + 328 - DC_GLOBAL_LOCK <? 8 then DC_CTX + 328 - DC_GLOBAL_LOCK else 0) with 0 in GLS4 by reflexivity.
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m4 DC_CTX 328 DC_IP12 ART4 GO_DC ltac:(unfold DC_IP12; clear; lia) ltac:(unfold DC_IP12; clear; lia) DCIP8) as IPS4.
  replace (if DC_CTX + 328 - DC_IP12 <? 8 then DC_CTX + 328 - DC_IP12 else 0) with 0 in IPS4 by reflexivity.
  assert (LKC4 : rw_cells asegs m4 LK (mutex_cells z64 z64)).
  { apply (rw_cells_agree asegs m m4 _ _ LKC); [| exact WM04]. intros x Hx. cbv beta in Hx. cbn [cells_size mutex_cells csize Nat.add] in Hx.
    apply G4; [apply (acl_live _ _ _ LK 40); [exact INLK | clear - Hx; lia] | left; clear - Hx RLK NUM; lia]. }
  destruct (af_client_consts RT AF Σ1 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  assert (AG4 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply MU4. cbn [outside]. clear - Hx H1. lia. }
  frb_keep FR3 AG4 WM4 FR4 HP FRB.
  (* [comment removed for export] *)
  pose proof (fx_s2_walk sp gp (Z_to_bv 64 0xba3ef0) u0 v1 u2 d1 d2 d3 (Z_to_bv 64 0x7fff8000) b5 b6 b7 s2 (Z_to_bv 64 f) (Z_to_bv 64 f) s7 s8 s9 s10 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 F2 fc2 m4 12 AD LK f lo pd j0 j1 j2 j3 j4 j6 j8 j9 g1 g2
                HP F0 ltac:(clear - FLO LOW; lia) ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) eq_refl
                ltac:(clear - PHI PAD; lia) ltac:(clear - RP LOW ADN; lia)
                UT4 SHC4 GL4 LKHI LKAL ltac:(clear - RLK LOW; lia) LKC4 GLS4 IPC4 IPS4 FR4 ST4 MI4) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (g4 & g5 & gs2 & m5 & -> & MU5 & WM5 & MI5 & FR5 & ST5 & LKC5) & Hc5'). clear Hc5.
  fold usp in MU5, FR5, ST5, Hc5'. fold usp1 in FR5, ST5, Hc5'.
  pose proof (wmono_trans asegs _ _ _ WM04 WM5) as WM05.
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 (usp - 320) ART4 ltac:(rewrite SP1; clear - NUM; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply acl_stack. unfold USTACK_TOP in *. clear - Hin NUM. lia.
    - apply (acl_live _ _ _ LK 40); [exact INLK1 | clear - Hin; lia]. }
  assert (B5 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (NX_W AD LK) (bv_unsigned x) -> m5 x = m x).
  { intros x Hx Ho. unfold NX_W in Ho. cbn [outside] in Ho. destruct (cl_split RT AF Σ m usp 352 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx) as [Hi|Lo].
    - rewrite (MU5 x ltac:(cbn [outside]; clear - Hi Ho; lia)). exact (G4 x Hx ltac:(right; exact Hi)).
    - rewrite (MU5 x ltac:(cbn [outside]; clear - Lo Ho; lia)). exact (G4 x Hx ltac:(left; exact Lo)). }
  assert (AG05 : agree_on (fun x => usp <= x < USTACK_TOP) m m5).
  { intros x Hx. cbv beta in Hx. apply B5; [apply acl_stack; exact Hx|]. unfold NX_W. cbn [outside]. clear - Hx RP RLK NUM PAD ADN. lia. }
  assert (CLE5 : cl_env m5 lb canary).
  { apply (cl_env_agree m m5 _ _ CLE). intros x Hx. destruct (STA _ (cl_cell_static _ Hx)) as (Hc & Ho & _). exact (B5 x Hc Ho). }
  pose proof FR5 as SV5. apply nxb_saved in SV5; [| exact HP | unfold c8s; repeat constructor].
  replace (usp1 + 176 + pd) with (usp - 16) in SV5 by (unfold usp1; clear; lia).
  destruct (cl_chain_call (rt_cg RT Σ) e_free_ex_data_A e_CRYPTO_free SITE_fx_free m m5 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG05
              ltac:(fold usp; exact SV5)
              ltac:(rewrite EU1; fold usp; unfold usp1; clear - HP; lia) SPT) as (CTX5 & UWC5).
  rewrite <- CG1 in CTX5.
  (* [comment removed for export] *)
  apply (C_FRN Σ1 PMc (Z_to_bv 64 SITE_fx_free) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 v1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 0) (Z_to_bv 64 EXD_FILE) (Z_to_bv 64 411)
           (Z_to_bv 64 0) g4 g5 b6 b7 gs2 (Z_to_bv 64 f) (Z_to_bv 64 AD) (Z_to_bv 64 12) (Z_to_bv 64 f) s7 (Z_to_bv 64 DC_IP12)
           (Z_to_bv 64 DC_GLOBAL_LOCK) s10 (Z_to_bv 64 (f / 8 + 2147450880)) u3 u4 u5 u6 F2 fc2 m5 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ART5 MI5).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST5|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK HP; lia|].
    split; [unfold USTACK_TOP in *; clear - NUM HP; lia|]. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { rewrite (unsigned_lit SITE_fx_free) by (unfold SITE_fx_free; clear; lia). exact CTX5. }
  { exact UWC5. }
  { rewrite CG1. rewrite (unsigned_lit SITE_fx_free) by (unfold SITE_fx_free; clear; lia). apply (proj2 CGH). right; left; reflexivity. }
  { exact CLE5. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (v & Hc6).
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & CLE6) & Hc6'). clear Hc6.
  destruct RS6 as (x0 & x1 & x2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_fx_free) in Hc6' by (unfold SITE_fx_free; clear; lia).
  pose proof (wmono_trans asegs _ _ _ WM05 WM6) as WM06.
  assert (P56 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m6 x = m5 x).
  { intros x Hx. apply PRES6. rewrite LV1, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | intros e He; right; exact He | unfold usp1; clear - HP; lia]. }
  assert (AG6 : forall a k, (usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 248) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 32) ->
            agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H x Hx. cbv beta in Hx. apply PRES6. destruct H as [H|[H|H]].
    - left. clear - H Hx. lia.
    - apply (acl_frame _ _ _ f 2%nat); [exact INF | change (fs_size 2) with 256; clear - H Hx; lia].
    - apply (acl_fshadow _ _ _ f 2%nat); [exact INF | rewrite SHF; unfold shad, SHB; clear - H Hx; lia]. }
  assert (AG6s : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m5 m6) by (intros a k H1 H2; apply AG6; left; split; assumption).
  frb_keep FR5 AG6s WM6 FR6 HP FRB.
  assert (ADC6 : rw_cells asegs m6 AD [C8 z64; C8 z64]).
  { apply (rw_cells_agree asegs m2 m6 _ _ ADC2); [| exact (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 WM6)))].
    intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    assert (Hc : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)) by (apply (acl_live _ _ _ p n); [exact INP | clear - Hx PAD ADN; lia]).
    rewrite (P56 x Hc). rewrite (MU5 x ltac:(cbn [outside]; clear - Hx DPL PAD ADN RP NUM; lia)). rewrite (MU4 x ltac:(cbn [outside]; unfold usp1; clear - Hx PAD ADN RP NUM HP; lia)).
    apply MU3. cbn [outside]. unfold usp1. clear - Hx PFP SFP PAD ADN RP NUM HP. lia. }
  pose proof (proj2 (af_acc_live RT AF Σ1 m6 p n ART6 INP1)) as ACC6.
  pose proof (acc_shadow0 m6 p n (AD + 8) ACC6 PAL ltac:(clear - PHI; lia) ltac:(clear - PAD; lia) ltac:(clear - PAD ADN; Z.div_mod_to_equations; lia)) as ADS26.
  pose proof FR6 as SC6. apply nxb_slot7 in SC6; [| unfold c8s; repeat constructor].
  (* [comment removed for export] *)
  pose proof (fx_s3_walk (Z_to_bv 64 SITE_fx_free) sp gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 v h1 h2 h3 h4 h5 h6 h7 gs2 (Z_to_bv 64 f) (Z_to_bv 64 12)
                (Z_to_bv 64 f) s7 (Z_to_bv 64 DC_IP12) (Z_to_bv 64 DC_GLOBAL_LOCK) s10 (Z_to_bv 64 (f / 8 + 2147450880)) x3 x4 x5 x6
                F6 fc6 m6 AD lo pd
                HP ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)
                ltac:(clear - PHI PAD; lia) ADAL ltac:(clear - RP LOW ADN; lia) ADC6 ADS26 SC6 ST6 MI6) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & ST7 & ADC7) & Hc7'). clear Hc7.
  fold usp in MU7, ST7, Hc7'. fold usp1 in MU7, ST7, Hc7'.
  assert (AG7 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m6 m7).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply MU7. cbn [outside]. clear - Hx H1. lia. }
  frb_keep FR6 AG7 WM7 FR7 HP FRB.
  pose proof (wmono_trans asegs _ _ _ WM06 WM7) as WM07.
  assert (ART7 : ART RT Σ1 m7).
  { apply (af_frame RT AF Σ1 m6 m7 (usp1 - 128) ART6 ltac:(rewrite SP1; unfold usp1; clear - NUM HP; lia)); [| exact WM7].
    intros a Ha. apply MU7. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hin NUM HP. lia. }
  pose proof (af_acc_live RT AF Σ1 m7 p n ART7 INP1) as (WRP7 & ACC7).
  (* [comment removed for export] *)
  apply (MSET Σ1 PMc (Z_to_bv 64 SITE_fx_mset) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) x0 x1 x2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 AD) (Z_to_bv 64 0) (Z_to_bv 64 16) h3 h4 h5 h6 h7
           gs2 (Z_to_bv 64 f) (Z_to_bv 64 AD) (Z_to_bv 64 12) (Z_to_bv 64 f) s7 (Z_to_bv 64 DC_IP12)
           (Z_to_bv 64 DC_GLOBAL_LOCK) s10 (Z_to_bv 64 (f / 8 + 2147450880)) x3 x4 x5 x6 F6 fc6 m7 AD 16 (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl
           ltac:(clear - PHI PAD ADN RP SP0R; unfold USTACK_TOP, STACK_WIN, SEGTOP_A in *; lia) ltac:(clear; lia)).
  { split; [intros _; split; [exact (acc_sub asegs m7 p n AD 16 ACC7 PAD ADN) | left; exists p, n; split; [exact INP1 | clear - PAD ADN; lia]]|].
    split; [intros i Hi; apply (acl_live _ _ _ p n); [exact INP1 | clear - Hi PAD ADN; lia] | exact (wr_at_sub m7 p n AD 16 WRP7 PAD ADN ltac:(clear; lia))]. }
  { exact ART7. } { exact MI7. }
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST7|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK HP; lia|].
    split; [unfold USTACK_TOP in *; clear - NUM HP; lia|]. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ1 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ZER8) & Hc8'). clear Hc8.
  destruct RS8 as (y0 & y1 & y2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & y3 & y4 & y5 & y6 & F8 & fc8 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_fx_mset) in Hc8' by (unfold SITE_fx_mset; clear; lia).
  pose proof (wmono_trans asegs _ _ _ WM07 WM8) as WM08.
  assert (ADC8 : rw_cells asegs m8 AD [C8 z64; C8 z64]).
  { split; [split; [cbn; repeat split; reflexivity | exact ZER8] | exact (wr_at_wm m7 m8 AD _ (proj2 ADC7) WM8)]. }
  assert (P78 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (AD <= bv_unsigned x < AD + 16) -> m8 x = m7 x).
  { intros x Hx Hn. apply PRES8; [| exact Hn]. rewrite LV1, FRS1. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | intros e He; right; exact He | unfold usp1; clear - HP; lia]. }
  assert (AG8 : forall a k, (usp1 <= a /\ a + k <= USTACK_TOP) \/ (f <= a /\ a + k <= f + 248) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 32) ->
            agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H x Hx. cbv beta in Hx. apply PRES8; [| destruct H as [H|[H|H]]; unfold usp1 in *; clear - H Hx RP PAD ADN NUM HP PFP SFP; lia]. destruct H as [H|[H|H]].
    - left. clear - H Hx. lia.
    - apply (acl_frame _ _ _ f 2%nat); [exact INF | change (fs_size 2) with 256; clear - H Hx; lia].
    - apply (acl_fshadow _ _ _ f 2%nat); [exact INF | rewrite SHF; unfold shad, SHB; clear - H Hx; lia]. }
  assert (AG8s : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m7 m8) by (intros a k H1 H2; apply AG8; left; split; assumption).
  frb_keep FR7 AG8s WM8 FR8 HP FRB.
  (* [comment removed for export] *)
  assert (K38 : forall x : word, (f <= bv_unsigned x < f + 248) \/ (f / 8 + 2147450880 <= bv_unsigned x < f / 8 + 2147450880 + 32) -> m8 x = m3 x).
  { intros x Hx.
    assert (E8 : m8 x = m7 x).
    { destruct Hx as [Hx|Hx]; [exact (AG8 f 248 ltac:(right; left; clear; lia) x Hx) | exact (AG8 (f / 8 + 2147450880) 32 ltac:(right; right; clear; lia) x Hx)]. }
    assert (E6 : m6 x = m5 x).
    { destruct Hx as [Hx|Hx]; [exact (AG6 f 248 ltac:(right; left; clear; lia) x Hx) | exact (AG6 (f / 8 + 2147450880) 32 ltac:(right; right; clear; lia) x Hx)]. }
    rewrite E8. rewrite (MU7 x ltac:(cbn [outside]; unfold usp1; clear - Hx FLO NUM SHR HLO HP; lia)). rewrite E6.
    rewrite (MU5 x ltac:(cbn [outside]; clear - Hx PFL SFL FLO NUM SHR HLO; lia)).
    apply MU4. cbn [outside]. unfold usp1. clear - Hx FLO NUM SHR HLO HP. lia. }
  destruct (rw_cells_forget asegs m3 f _ (rw_cells_head m3 f _ _ FB3)) as (hj & HDR3). cbn [cells_size csize Nat.add] in HDR3.
  assert (HDR8 : rw_cells asegs m8 f [CB 8 hj]).
  { apply (rw_cells_agree asegs m3 m8 _ _ HDR3); [| exact (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 WM8))))].
    intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply K38. left. clear - Hx. lia. }
  destruct (rw_cells_forget asegs m3 _ _ SB3) as (sj' & SB3'). unfold fx_shadow_live in SB3'. cbn [cells_size csize Nat.add map app repeat] in SB3'.
  assert (SB8 : rw_cells asegs m8 (f / 8 + 2147450880) [CB 32 sj']).
  { apply (rw_cells_agree asegs m3 m8 _ _ SB3'); [| exact (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 WM8))))].
    intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply K38. right. clear - Hx. lia. }
  (* [comment removed for export] *)
  pose proof (fx_x1_walk (Z_to_bv 64 SITE_fx_mset) sp gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 (Z_to_bv 64 AD) i1 i2 i3 i4 i5 i6 i7 gs2 (Z_to_bv 64 AD) (Z_to_bv 64 12)
                s7 (Z_to_bv 64 DC_IP12) (Z_to_bv 64 DC_GLOBAL_LOCK) s10 y3 y4 y5 y6
                F8 fc8 m8 f lo pd hj sj'
                HP ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)
                F0 FIMG ltac:(clear - FLO LOW; lia) ltac:(clear - FSH; destruct FSH; [left | right]; lia) ST8 HDR8 SB8 MI8) as W5.
  fold usp usp1 in W5.
  cl_lift W5 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ1 _ _ c9 Hc9) as (ms9 & (ra1 & m9 & -> & MU9 & WM9 & MI9 & HDR9 & SB9) & Hc9'). clear Hc9.
  fold usp in Hc9'. fold usp1 in Hc9'.
  pose proof (wmono_trans asegs _ _ _ WM08 WM9) as WM09.
  assert (ART9 : ART RT Σ1 m9).
  { apply (af_frame RT AF Σ1 m8 m9 usp1 ART8 ltac:(rewrite SP1; unfold usp1; clear - NUM HP; lia)); [| exact WM9].
    intros a Ha. apply MU9. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 2%nat); [exact INF | change (fs_size 2) with 256; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ f 2%nat); [exact INF | rewrite SHF; unfold shad, SHB; clear - Hin; lia]. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ1 m9 f 2%nat (rt_frames RT Σ) ART9 FRS1) as (Σ2 & flg & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 2) with 256 in FW. replace (f + 256 - 8) with (f + 248) in FW by (clear; lia). rewrite SP1 in FLW.
  assert (FLLO : flg + 1 <= lo) by (clear - FLW LOW; lia).
  assert (AG9 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m8 m9).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply MU9. cbn [outside]. unfold usp1 in H1. clear - Hx H1 FLO NUM SHR HLO HP. lia. }
  frb_keep FR8 AG9 WM9 FR9 HP FRB.
  pose proof FR9 as FR9b. apply nxb_blob in FR9b; [| exact HP | unfold c8s; repeat constructor]. destruct FR9b as (lowj & FR9b).
  assert (ST9 : stk asegs m9 lo usp1).
  { apply (stk_agree_nw asegs m8 m9 _ _ ST8). intros x Hx. cbv beta in Hx. unfold usp1 in Hx. apply MU9. cbn [outside]. clear - Hx FLO LOW NUM SHR HP. lia. }
  (* [comment removed for export] *)
  pose proof (fx_x2_walk ra1 ra sp gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 (Z_to_bv 64 (-11)) i1 i2 i3 i4 i5 i6 i7 gs2 (Z_to_bv 64 AD) (Z_to_bv 64 12)
                (Z_to_bv 64 f) s7 (Z_to_bv 64 DC_IP12) (Z_to_bv 64 DC_GLOBAL_LOCK) s10 (Z_to_bv 64 (f / 8 + 2147450880)) y3 y4 y5 y6
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F8 fc8 m9 f flg lo pd lowj
                HP ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)
                F0 ltac:(clear - FLO LOW; lia) FL0 FLLO ST9 FR9b FW FLC MI9) as W6.
  fold usp usp1 in W6.
  cl_lift W6 Hc9' c10 Hc10.
  destruct (ASTA_unpack RT Σ1 _ _ c10 Hc10) as (ms10 & (z0 & z1 & z2 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & z3 & z4 & z5 & z6 & m10 & -> & MU10 & WM10 & MI10 & ST10 & FLC10) & Hc10'). clear Hc10.
  fold usp in ST10.
  destruct (REL m10 MU10 WM10 FLC10) as (ART10 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).
  (* [comment removed for export] *)
  assert (NFL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> x <> flg).
  { intros x Hx Ex. subst x. destruct Hx as [H|H]; [unfold USTACK_TOP, RT_STACK, STACK_WIN in *; clear - H FLW NUM; lia|].
    apply NAC. right. rewrite LV1, FRS1.
    destruct H as [H|[H|[H|H]]]; [left; exact H | right; left; exact H
      | right; right; left; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]
      | right; right; right; destruct H as (f' & k' & Hin & R); exists f', k'; split; [right; exact Hin | exact R]]. }
  assert (A810 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m10 x = m8 x).
  { intros x Hx.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 2%nat usp _ ART2 FRS1 LV1 SP1 ltac:(clear - NUM; lia) Hx) as (N1 & N2).
    change (fs_size 2) with 256 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU10 x ltac:(cbn [outside]; split; [pose proof (NFL _ Hx); lia | exact I])).
    apply MU9. cbn [outside]. clear - N1 N2. lia. }
  assert (B10 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (NX_W AD LK) (bv_unsigned x) -> m10 x = m x).
  { intros x Hx Ho. rewrite (A810 x Hx). rewrite (P78 x Hx ltac:(unfold NX_W in Ho; cbn [outside] in Ho; clear - Ho; lia)).
    destruct (cl_split RT AF Σ m usp 352 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx) as [Hi|Lo].
    - rewrite (MU7 x ltac:(cbn [outside]; unfold usp1; clear - Hi HP; lia)). rewrite (P56 x Hx). exact (B5 x Hx Ho).
    - rewrite (MU7 x ltac:(cbn [outside]; unfold usp1; clear - Lo HP; lia)). rewrite (P56 x Hx). exact (B5 x Hx Ho). }
  apply Hk. exists Σ2.
  split; [| unfold rts_same; rewrite LV3, LV1, FRS3, SP3, SP1, CR3, CR1, CG3, CG1; repeat split; first [reflexivity | lia]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ1 Σ2 PMc _ c10 Hc10' AL3 AM3)|]. intros ms <-. exists (Z_to_bv 64 flg), m10.
  split; [exists z0, z1, z2, n1, n2, n3, n4, n5, n6, n7, z3, z4, z5, z6, F8, fc8; reflexivity|].
  split; [split; [exact ART10 | split; [exact MI10 | split; [exact (wmono_trans asegs _ _ _ WM09 WM10) | exact ST10]]]|].
  split; [exact B10|].
  split; [| split; [| split]].
  - apply (cl_env_agree m6 m10 _ _ CLE6). intros x Hx. destruct (STA _ (cl_cell_static _ Hx)) as (Hc & Ho & Hl).
    rewrite (A810 x Hc). rewrite (P78 x Hc ltac:(unfold NX_W in Ho; cbn [outside] in Ho; clear - Ho; lia)). apply MU7. cbn [outside]. unfold usp1. clear - Hl HP. lia.
  - apply (exd_stat_agree m m10 kd LK EST). intros x Hx. destruct (STA _ (exd_fp_static kd _ KD Hx)) as (Hc & Ho & _). exact (B10 x Hc Ho).
  - apply (rw_cells_agree_nw asegs m8 m10 _ _ ADC8). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A810. apply (acl_live _ _ _ p n); [exact INP | clear - Hx PAD ADN; lia].
  - apply (rw_cells_agree_nw asegs m5 m10 _ _ LKC5). intros x Hx. cbv beta in Hx. cbn [cells_size mutex_cells csize Nat.add] in Hx.
    assert (Hc : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)) by (apply (acl_live _ _ _ LK 40); [exact INLK | clear - Hx; lia]).
    rewrite (A810 x Hc). rewrite (P78 x Hc ltac:(clear - Hx DPL PAD ADN; lia)). rewrite (MU7 x ltac:(cbn [outside]; unfold usp1; clear - Hx RLK NUM HP; lia)). exact (P56 x Hc).
Qed.
End CExd.
