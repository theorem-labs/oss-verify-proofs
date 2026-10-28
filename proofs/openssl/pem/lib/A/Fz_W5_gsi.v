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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Th_errno Fz_T_sa Fz_W5_glx Fz_W5_icb Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_get_state : Z := 0x1fdc48.
Definition SITE_gsi_icb : Z := 0x1fdcac.        (* [comment removed for export] *)
Definition ERRNO_A : Z := 0xba3e4c.             (* [comment removed for export] *)
Definition TSD_MAIN_A : Z := 0xbc5298.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition icstat (m : mem) (od : word) : Prop :=
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m G_IC_OPTSDONE [C8 od]
  /\ rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)].

(* [comment removed for export] *)
Definition errchain (m : mem) (k MK SA NODES E LV : Z) (pad top ne : word) : Prop :=
  rw_cells asegs m G_TL_MASTER_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m G_TL_MASTER_KEY [C4 (Z_to_bv 64 k)] /\ 1 <= k < 128
  /\ rw_cells asegs m (TSD_MAIN_A + 8 * k) [C8 (Z_to_bv 64 MK)]
  /\ rw_cells asegs m (MK + 24) [C8 (Z_to_bv 64 SA)]
  /\ rw_cells asegs m SA (sa_hdr (Z_to_bv 64 LV) pad top ne (Z_to_bv 64 NODES)) /\ bv_unsigned ne <> 0 /\ 0 <= LV < 2
  /\ rw_cells asegs m NODES [C8 (Z_to_bv 64 E)].

Lemma icstat_agree : forall (m m' : mem) od, icstat m od -> (forall a k, 0xb9f200 <= a -> a + k <= 0xb9f2e8 -> agree_on (fun x => a <= x < a + k) m m') ->
  wmono asegs m m' -> icstat m' od.
Proof.
  intros m m' od (A & B & C & D) AG WM. unfold icstat, G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in *.
  repeat split; (eapply rw_cells_agree; [eassumption | apply AG; cbn [cells_size csize Nat.add]; lia | exact WM]).
Qed.

Lemma errchain_agree : forall (m m' : mem) k MK SA NODES E LV pad top ne, errchain m k MK SA NODES E LV pad top ne ->
  (forall a n, (0xb9f500 <= a /\ a + n <= 0xb9f528) \/ (TSD_MAIN_A + 8 <= a /\ a + n <= TSD_MAIN_A + 1024) \/ (MK <= a /\ a + n <= MK + 72) \/ (SA <= a /\ a + n <= SA + 32)
               \/ (NODES <= a /\ a + n <= NODES + 128) -> agree_on (fun x => a <= x < a + n) m m') ->
  wmono asegs m m' -> errchain m' k MK SA NODES E LV pad top ne.
Proof.
  intros m m' k MK SA NODES E LV pad top ne (A & B & HK & C & D & G & HNE & HLV & H) AG WM. unfold errchain, G_TL_MASTER_ONCE, G_TL_MASTER_KEY, TSD_MAIN_A, sa_hdr in *.
  split; [eapply rw_cells_agree; [exact A | apply AG; cbn [cells_size csize Nat.add]; lia | exact WM]|].
  split; [eapply rw_cells_agree; [exact B | apply AG; cbn [cells_size csize Nat.add]; lia | exact WM]|]. split; [exact HK|].
  split; [eapply rw_cells_agree; [exact C | apply AG; cbn [cells_size csize Nat.add]; lia | exact WM]|].
  split; [eapply rw_cells_agree; [exact D | apply AG; cbn [cells_size csize Nat.add]; lia | exact WM]|].
  split; [eapply rw_cells_agree; [exact G | apply AG; cbn [cells_size csize Nat.add]; lia | exact WM]|]. split; [exact HNE|]. split; [exact HLV|].
  eapply rw_cells_agree; [exact H | apply AG; cbn [cells_size csize Nat.add]; lia | exact WM].
Qed.

(* [comment removed for export] *)
Definition gsi_s0_post (sp gp tp t0 t1 t2 s2 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ev : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_gsi_icb) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 1)
                 (Z_to_bv 64 OPT_BASE_ONLY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x7fff8000) ev s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_init_crypto) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma gsi_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (e : word),
  tp = Z_to_bv 64 0xba3ef0 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m ERRNO_A [C4 e] -> acc asegs m 0xba3e48 8 -> mem_inv asegs m ->
  evt asegs (gsi_s0_post sp gp tp t0 t1 t2 s2' s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_get_state) fc None m (seg_rom asegs)).
Proof.
  intros until e. intros -> ST HLO HLOS SPH UT SHC ERC ERA MI. unfold e_get_state, ERRNO_A, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 48, SP)]) by sh_fp_lia.
  assert (EAL : 0xba3e48 mod 8 = 0) by reflexivity.
  carve_frame 48%nat ST.
  do 8 zstep. do 4 zstep. zstep. th_if_lit. zstep.
  pose proof errno_location_proof as EL. unfold errno_location_stmt in EL.
  eapply evt_cut; [apply EL; rewrite unsigned_lit by lia; lia|]. intros ms' ->. cbv delta [mkR]. th_ret_lit.
  rewrite (unsigned_lit 0xba3ef0) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (acc_granule0_ro mX 12205640 8 12205640 (acc_munch_sh _ m mX _ _ ERA MU HWS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)) as SH0 end.
  unfold shad, SHB in SH0. replace (12205640 / 8 + 2147450880) with 2148976585 in SH0 by reflexivity. change z8 with (Z_to_bv 8 0) in SH0.
  do 3 zstep. zstep. th_if_lit. zstep.
  do 4 zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gsi_s0_post, SITE_gsi_icb, OPT_BASE_ONLY, e_init_crypto. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition gsi_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 e' : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (ERRNO_A, ERRNO_A + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' ERRNO_A [C4 e'].

Lemma gsi_s1_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2 s2' s3' s4' ev s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (e : word) (k MK SA NODES E LV : Z) (pad top ne : word),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m ERRNO_A [C4 e] -> acc asegs m 0xba3e48 8 ->
  errchain m k MK SA NODES E LV pad top ne ->
  ro_cells asegs m (G_TL_MASTER_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 4)] ->
  rw_cells asegs m 0xba3e98 [C8 (Z_to_bv 64 TSD_MAIN_A)] ->
  acc asegs m MK 72 -> 0 < MK -> MK mod 8 = 0 -> MK + 72 <= lo ->
  acc asegs m SA 32 -> 0 < SA -> SA mod 8 = 0 -> SA + 32 <= lo ->
  acc asegs m NODES 128 -> 0 < NODES -> NODES mod 8 = 0 -> NODES + 128 <= lo ->
  0 < E -> E + 904 <= lo ->
  mem_inv asegs m ->
  evt asegs (gsi_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 F fc E lo m)
    (MS (mkR (Z_to_bv 64 SITE_gsi_icb) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 1)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x7fff8000) ev s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_gsi_icb) fc None m (seg_rom asegs)).
Proof.
  intros until ne. intros ST HLO HLOS SPH UT SHC FR ERC ERA CH KSB TSD ACCM MK0 MKAL MKLO ACCS SA0 SAAL SALO ACCN N0 NAL NLO E0 ELO MI.
  unfold SITE_gsi_icb, ERRNO_A, TSD_MAIN_A, g_shadow_memory_dynamic_address in *.
  destruct CH as (ONCE & KEY & HK & TSK & SLOT & SAC & HNE & HLV & LEAF). unfold G_TL_MASTER_ONCE, G_TL_MASTER_KEY, sa_hdr in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 112, SP); (12205644, 12205644 + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 112, SP); (12205644, 12205644 + 4)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 112, SP); (12205644, 12205644 + 4)]) by sh_fp_lia.
  assert (EU1 : bv_unsigned (Z_to_bv 64 (SP + -48)) = SP + -48) by (apply unsigned_lit; lia).
  zstep. th_if_lit. do 2 zstep. zstep.
  tcall (T_get_local_ex_steady_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 12341912 k MK SA LV NODES 4 pad top ne (Z_to_bv 64 E));
    [ reflexivity | reflexivity | exact (proj1 ONCE) | exact (proj1 KEY) | lia | exact KSB | right; reflexivity
    | exact (proj1 TSD) | lia | lia | exact (proj1 TSK) | lia | lia
    | exact (proj1 SLOT) | exact ACCM | exact MK0 | exact MKAL | exact MKLO
    | exact (proj1 SAC) | exact ACCS | exact SA0 | exact SAAL | exact SALO | exact HNE | exact HLV
    | exact (proj1 LEAF) | exact ACCN | exact N0 | exact NAL | exact NLO
    | exact UT | exact SHC | exact ST | lia | lia | lia | exact MI | ].
  cbv beta delta [mkR].
  zstep. zstep. if_cases KM1; zify_cond KM1. { exfalso. rewrite ?unsigned_lit in KM1 by lia. lia. }
  zstep. zstep. if_cases KE0; zify_cond KE0. 2:{ exfalso. lia. }
  zstep. th_if_lit. zstep.
  pose proof errno_location_proof as EL. unfold errno_location_stmt in EL.
  eapply evt_cut; [apply EL; rewrite unsigned_lit by lia; lia|]. intros ms' ->. cbv delta [mkR]. th_ret_lit.
  rewrite (unsigned_lit 0xba3ef0) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (acc_granule0_ro mX 12205640 8 12205640 (acc_munch_sh _ m mX _ _ ERA MU HWS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)) as SH0 end.
  unfold shad, SHB in SH0. replace (12205640 / 8 + 2147450880) with 2148976585 in SH0 by reflexivity. change z8 with (Z_to_bv 8 0) in SH0.
  do 3 zstep. zstep. th_if_lit. zstep. clear SH0.
  do 2 zstep. do 6 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gsi_s1_post. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| eassumption].
Qed.

Section CGsi.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ICB : init_crypto_base_stmt RT.
(* [comment removed for export] *)
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m 0xba3e98 [C8 (Z_to_bv 64 0xbc5298)].
Hypothesis ERRNO_ACC : forall Σ m, ART RT Σ m -> acc asegs m 0xba3e48 8.
Hypothesis GO_mkey : GOBJ G_TL_MASTER_KEY 4.

Definition get_state_steady_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (od e : word) (k MK SA NODES E LV : Z) (pad top ne : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 1 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 176 <= bv_unsigned sp ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  icstat m od -> rw_cells asegs m ERRNO_A [C4 e] -> errchain m k MK SA NODES E LV pad top ne ->
  In (MK, 72) (rt_live RT Σ) -> In (SA, 32) (rt_live RT Σ) -> In (NODES, 128) (rt_live RT Σ) -> In (E, 904) (rt_live RT Σ) ->
  MK mod 8 = 0 -> SA mod 8 = 0 -> NODES mod 8 = 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_get_state m)))
    (fun c => exists (Σ' : rts RT) (e' : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 E) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(ERRNO_A, ERRNO_A + 4)] m m'
           /\ icstat m' od /\ rw_cells asegs m' ERRNO_A [C4 e'] /\ errchain m' k MK SA NODES E LV pad top ne) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem get_state_steady_cps : get_state_steady_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo od e k MK SA NODES E LV pad top ne
    FDO MST -> -> ART0 MI0 CALL HSTK Hfr Hcr ICS ERC CH INM INS INN INE MKAL SAAL NAL.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 176 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -48).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  pose proof (gsi_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo e
                eq_refl ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC ERC (ERRNO_ACC Σ m ART0) MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (ev & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  assert (ICS1 : icstat m1 od).
  { apply (icstat_agree m m1 od ICS); [| exact WM1]. intros a n H1 H2. apply (agree_of_munch _ m m1 _ MU1). intros x Hx. cbv beta in Hx. cbn [outside]. unfold RT_STACK in *. lia. }
  destruct ICS1 as (STP1 & OD1 & ONCE1 & BRET1).
  apply (C_ICB Σ PMc (Z_to_bv 64 SITE_gsi_icb) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 1) (Z_to_bv 64 OPT_BASE_ONLY) (Z_to_bv 64 0)
           a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x7fff8000) ev s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo od FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. unfold usp1. lia. }
  { exact Hfr. } { exact Hcr. } { exact STP1. } { exact OD1. } { exact ONCE1. } { exact BRET1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ICS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_gsi_icb) in Hc2' by (unfold SITE_gsi_icb; lia).
  (* [comment removed for export] *)
  assert (AG02 : forall a n, (usp <= a /\ a + n <= USTACK_TOP) \/ (0xb9f200 <= a /\ a + n <= 0xb9f848) \/ (0xbc52a0 <= a /\ a + n <= 0xbc5698) \/ (ERRNO_A <= a /\ a + n <= ERRNO_A + 4)
            \/ (MK <= a /\ a + n <= MK + 72) \/ (SA <= a /\ a + n <= SA + 32) \/ (NODES <= a /\ a + n <= NODES + 128) -> agree_on (fun x => a <= x < a + n) m m2).
  { pose proof (af_live_range RT AF Σ m MK 72 ART0 INM) as R1. pose proof (af_live_range RT AF Σ m SA 32 ART0 INS) as R2. pose proof (af_live_range RT AF Σ m NODES 128 ART0 INN) as R3.
    intros a n H x Hx. cbv beta in Hx. unfold ERRNO_A in H.
    rewrite (PRES2 x).
    - refine (agree_of_munch _ m m1 (fun y => a <= y < a + n) MU1 _ x Hx). intros y Hy. cbv beta in Hy. cbn [outside]. unfold STACK_WIN, USTACK_TOP, RT_STACK in *. lia.
    - destruct H as [H|[H|[H|[H|[H|[H|H]]]]]].
      + left. unfold usp1. lia.
      + right; left. apply client_static_intro. lia.
      + right; left. apply client_static_intro. lia.
      + right; left. apply client_static_intro. lia.
      + right; right; left. exists MK, 72. split; [exact INM | lia].
      + right; right; left. exists SA, 32. split; [exact INS | lia].
      + right; right; left. exists NODES, 128. split; [exact INN | lia]. }
  assert (WM02 : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM2).
  assert (CH2 : errchain m2 k MK SA NODES E LV pad top ne).
  { apply (errchain_agree m m2 _ _ _ _ _ _ _ _ _ CH); [| exact WM02]. intros a n H. apply AG02. unfold TSD_MAIN_A in H. destruct CH as (_ & _ & HK & _). lia. }
  assert (ERC2 : rw_cells asegs m2 ERRNO_A [C4 e]) by (apply (rw_cells_agree asegs m m2 _ _ ERC); [apply AG02; cbn [cells_size csize Nat.add]; lia | exact WM02]).
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2) by (intros a n H1 H2 x Hx; cbv beta in Hx; apply PRES2; left; lia).
  cl_keep FR1 AG2 WM2 FR2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (INM2 : In (MK, 72) (rt_live RT Σ1)) by (rewrite LV1; exact INM). assert (INS2 : In (SA, 32) (rt_live RT Σ1)) by (rewrite LV1; exact INS).
  assert (INN2 : In (NODES, 128) (rt_live RT Σ1)) by (rewrite LV1; exact INN). assert (INE2 : In (E, 904) (rt_live RT Σ1)) by (rewrite LV1; exact INE).
  pose proof (af_live_range RT AF Σ1 m2 MK 72 ART2 INM2) as RM. pose proof (af_live_range RT AF Σ1 m2 SA 32 ART2 INS2) as RS.
  pose proof (af_live_range RT AF Σ1 m2 NODES 128 ART2 INN2) as RN. pose proof (af_live_range RT AF Σ1 m2 E 904 ART2 INE2) as RE. rewrite SP1 in RM, RS, RN, RE.
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m2 _ _ G_TL_MASTER_KEY ART2 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KSB2. cbn [Z.ltb Z.sub Z.add Z.leb] in KSB2.
  (* [comment removed for export] *)
  pose proof (gsi_s1_walk ra sp gp u0 u1 u2 s0 s1 b1 b2 b3 b4 b5 b6 b7 s2 s2 s3 s4 ev s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo e k MK SA NODES E LV pad top ne
                ST2 ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT2 SHC2 FR2 ERC2 (ERRNO_ACC Σ1 m2 ART2) CH2 KSB2 (TSD Σ1 m2 ART2)
                (proj2 (af_acc_live RT AF Σ1 m2 MK 72 ART2 INM2)) ltac:(lia) MKAL ltac:(lia)
                (proj2 (af_acc_live RT AF Σ1 m2 SA 32 ART2 INS2)) ltac:(lia) SAAL ltac:(lia)
                (proj2 (af_acc_live RT AF Σ1 m2 NODES 128 ART2 INN2)) ltac:(lia) NAL ltac:(lia) ltac:(lia) ltac:(lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & e' & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERC3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3.
  assert (ART3 : ART RT Σ1 m3).
  { apply (cl_seg_ART RT AF Σ1 m2 m3 usp 112 [(ERRNO_A, ERRNO_A + 4)] ART2 ltac:(rewrite SP1; lia) ltac:(unfold USTACK_TOP in *; lia)); [| | exact WM3].
    - eapply munch_weaken; [| exact MU3]. intros y Hy. unfold ERRNO_A in *. cbn [outside app] in *. lia.
    - intros x Hx. apply client_static_intro. unfold ERRNO_A in Hx. cbn [outside] in Hx. lia. }
  apply Hk. exists Σ1, e'.
  split; [| split; [exact LV1 | split; [exact FRS1 | split; [exact SP1 | split; [exact CR1 | exact CG1]]]]].
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3.
  split; [exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F2, fc2; reflexivity|].
  split; [split; [exact ART3 | split; [exact MI3 | split; [exact (wmono_trans asegs _ _ _ WM02 WM3) | exact ST3]]]|].
  assert (AG23 : forall a n, (usp <= a /\ a + n <= USTACK_TOP) \/ (a + n <= usp - 112 /\ (a + n <= ERRNO_A \/ ERRNO_A + 4 <= a)) -> agree_on (fun x => a <= x < a + n) m2 m3).
  { intros a n H x Hx. cbv beta in Hx. refine (agree_of_munch _ m2 m3 (fun y => a <= y < a + n) MU3 _ x Hx). intros y Hy. cbv beta in Hy. unfold ERRNO_A, RT_STACK in *. cbn [outside]. lia. }
  split.
  { intros a Ha Ho. unfold ERRNO_A in Ho. cbn [outside] in Ho.
    pose proof (cl_split RT AF Σ m usp 176 _ ART0 ltac:(lia) ltac:(lia) Ha) as N4.
    rewrite (MU3 a ltac:(unfold ERRNO_A; cbn [outside]; lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | unfold usp1; lia])).
    exact (PR1 a Ha I). }
  pose proof (af_live_range RT AF Σ m MK 72 ART0 INM) as R1. pose proof (af_live_range RT AF Σ m SA 32 ART0 INS) as R2. pose proof (af_live_range RT AF Σ m NODES 128 ART0 INN) as R3.
  split; [apply (icstat_agree m2 m3 od ICS2); [intros a n H1 H2; apply AG23; right; unfold ERRNO_A, RT_STACK in *; lia | exact WM3]|].
  split; [exact ERC3|].
  apply (errchain_agree m2 m3 _ _ _ _ _ _ _ _ _ CH2); [| exact WM3]. intros a n H. apply AG23. right. unfold TSD_MAIN_A, ERRNO_A, STACK_WIN, RT_STACK, SEGTOP_A in *. destruct CH as (_ & _ & HK & _). lia.
Qed.

End CGsi.
