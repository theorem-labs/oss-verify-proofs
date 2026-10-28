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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Th_tsd Th_key Th_once Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_T_master Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0 Fz_I3_glx0 Fz_G_OSSL_ERR_STATE_new Fz_T_its Fz_I3_icfast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation TP_A := (0xba3ef0)%Z (only parsing).

Definition SITE_eg_glx : Z := 0x1fdcbc.        (* [comment removed for export] *)
Definition SITE_eg_slx1 : Z := 0x1fdcdc.       (* [comment removed for export] *)
Definition SITE_eg_new : Z := 0x1fdce4.        (* [comment removed for export] *)
Definition SITE_eg_its : Z := 0x1fdd00.        (* [comment removed for export] *)
Definition SITE_eg_slx2 : Z := 0x1fdd14.       (* [comment removed for export] *)
Definition SITE_eg_icf : Z := 0x1fdd24.        (* [comment removed for export] *)
Definition ERR_DEL_THREAD_STATE : Z := 0x1ff1f0. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition eg_w1_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 a7 t0 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo SA P : Z) (pad top : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t1' a1' a2' a3' a4' a5' a6' top' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_eg_new) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1' t2 sp (Z_to_bv 64 0)
                 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7 (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_OSSL_ERR_STATE_new) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp - 48); (SA + 8, SA + 24); (P, P + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
    /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 1) (Z_to_bv 64 P))
    /\ rw_cells asegs m' P [C8 (Z_to_bv 64 (-1))].

Lemma eg_w1 : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (k MK SA P : Z) (pad top : word),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 160 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> ro_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 1 <= k < 128 ->
  ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 4)] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] -> ro_cells asegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] ->
  0x10007fff8000 <= MK -> MK mod 8 = 0 -> MK + 72 <= lo -> acc asegs m MK 72 -> ro_cells asegs m (MK + 24) [C8 (Z_to_bv 64 SA)] ->
  0x10007fff8000 <= SA -> SA mod 8 = 0 -> SA + 32 <= lo -> acc asegs m SA 32 -> rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top (Z_to_bv 64 0) (Z_to_bv 64 P)) ->
  0x10007fff8000 <= P -> P mod 8 = 0 -> P + 128 <= lo -> acc asegs m P 128 -> rw_cells asegs m P [C8 (Z_to_bv 64 0)] -> (SA + 32 <= P \/ P + 128 <= SA) ->
  mem_inv asegs m ->
  evt asegs (eg_w1_post sp gp (Z_to_bv 64 TP_A) s5 s6 s7 s8 s9 s10 s11 a7 t0 t2 t3 t4 t5 t6 F fc lo SA P pad top m)
    (MS (mkR (Z_to_bv 64 SITE_gsi_icb) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 0)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_gsi_icb) fc None m (seg_rom asegs)).
Proof.
  intros until top. intros ST HLO HLOS SPH UT SHC ONCE KEY HK KSB TSD TSK MKHI MKAL MKLO ACCM SLOT SAHI SAAL SALO ACCS SAC PHI PAL PLO ACCP PC DISJ MI.
  unfold SITE_gsi_icb, g_shadow_memory_dynamic_address, sa_hdr in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 160, SP - 48); (SA + 8, SA + 24); (P, P + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 160, SP - 48); (SA + 8, SA + 24); (P, P + 8)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 160, SP - 48); (SA + 8, SA + 24); (P, P + 8)]) by sh_fp_lia.
  assert (EU1 : bv_unsigned (Z_to_bv 64 (SP + -48)) = SP + -48) by (apply unsigned_lit; lia).
  zstep. th_if_lit. do 2 zstep. zstep.
  tcall (T_get_local_ex_empty_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN k MK SA 4 (Z_to_bv 64 1) pad top (Z_to_bv 64 P));
    [ reflexivity | reflexivity | exact ONCE | exact KEY | lia | exact KSB | right; reflexivity
    | exact TSD | lia | lia | exact TSK | lia | lia
    | replace (MK + 8 * 3) with (MK + 24) by lia; exact SLOT | exact ACCM | lia | exact MKAL | exact MKLO
    | exact (proj1 SAC) | exact ACCS | lia | exact SAAL | exact SALO
    | exact UT | exact SHC | exact ST | lia | lia | lia | exact MI | ].
  cbv beta delta [mkR].
  zstep. zstep. if_cases KM1; zify_cond KM1. { exfalso. rewrite ?unsigned_lit in KM1 by lia. lia. }
  zstep. zstep. if_cases KE0; zify_cond KE0. { exfalso. rewrite ?unsigned_lit in KE0 by lia. lia. }
  do 3 zstep. zstep.
  tcall (T_set_local_ex_steady_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN k 3 MK SA P 4 pad top (Z_to_bv 64 0) (Z_to_bv 64 0));
    first [reflexivity | eassumption | lia | right; reflexivity | exact (ut_munch _ m _ UT MU HWU) | idtac].
  all: try (eapply acc_munch_sh; [eassumption | exact MU | exact HWS | lia | lia]).
  cbv beta delta [mkR].
  assert (SD : sa_delta (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = 1) by (vm_compute; reflexivity).
  rewrite SD in PC1. clear SD. change (Z_to_bv 64 (0 + 1)) with (Z_to_bv 64 1) in PC1.
  zstep; th_if_lit. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold eg_w1_post, SITE_eg_new, e_OSSL_ERR_STATE_new, sa_hdr. apply evt_done. do 9 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside app]; intros; lia|].
  repeat (split; [eassumption|]); eassumption.
Qed.

Lemma eg_sa_delta_nz : forall E, 0 < E < 2 ^ 64 -> sa_delta (Z_to_bv 64 E) (Z_to_bv 64 (-1)) = 0.
Proof.
  intros E HE. unfold sa_delta.
  assert (B : bv_eqb (Z_to_bv 64 E) (Z_to_bv 64 0) = false) by (rewrite bv_eqb_Z; apply Z.eqb_neq; rewrite !unsigned_lit by lia; lia).
  rewrite B. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma eg_w2 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (E : Z),
  0 < E < 2 ^ 64 -> mem_inv asegs m ->
  evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 SITE_eg_its) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 0)
                                     (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 ERR_DEL_THREAD_STATE) a3 a4 a5 a6 a7 (Z_to_bv 64 E) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 e_its) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_eg_new) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 0)
             (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_eg_new) fc None m (seg_rom asegs)).
Proof.
  intros until E. intros HE MI. unfold SITE_eg_new, SITE_eg_its, ERR_DEL_THREAD_STATE, e_its in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep; if_cases KE; zify_cond KE. { exfalso. rewrite ?unsigned_lit in KE by lia. lia. }
  do 5 zstep. zstep.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition eg_w3_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t0 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo SA P E : Z) (pad top : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t1' a2' a3' top' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_eg_icf) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1' t2 sp (Z_to_bv 64 0)
                 (Z_to_bv 64 2) (Z_to_bv 64 0) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 E) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_init_crypto) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp - 48); (SA + 8, SA + 24); (P, P + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
    /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 1) (Z_to_bv 64 P))
    /\ rw_cells asegs m' P [C8 (Z_to_bv 64 E)].

Lemma eg_w3 : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (k MK SA P E : Z) (pad top : word),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 160 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> ro_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 1 <= k < 128 ->
  ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 4)] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] -> ro_cells asegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] ->
  0x10007fff8000 <= MK -> MK mod 8 = 0 -> MK + 72 <= lo -> acc asegs m MK 72 -> ro_cells asegs m (MK + 24) [C8 (Z_to_bv 64 SA)] ->
  0x10007fff8000 <= SA -> SA mod 8 = 0 -> SA + 32 <= lo -> acc asegs m SA 32 -> rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top (Z_to_bv 64 1) (Z_to_bv 64 P)) ->
  0x10007fff8000 <= P -> P mod 8 = 0 -> P + 128 <= lo -> acc asegs m P 128 -> rw_cells asegs m P [C8 (Z_to_bv 64 (-1))] -> (SA + 32 <= P \/ P + 128 <= SA) ->
  0 < E < 2 ^ 64 -> mem_inv asegs m ->
  evt asegs (eg_w3_post sp gp (Z_to_bv 64 TP_A) s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t0 t2 t3 t4 t5 t6 F fc lo SA P E pad top m)
    (MS (mkR (Z_to_bv 64 SITE_eg_its) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 0)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 E) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_eg_its) fc None m (seg_rom asegs)).
Proof.
  intros until top. intros ST HLO HLOS SPH UT SHC ONCE KEY HK KSB TSD TSK MKHI MKAL MKLO ACCM SLOT SAHI SAAL SALO ACCS SAC PHI PAL PLO ACCP PC DISJ HE MI.
  unfold SITE_eg_its, g_shadow_memory_dynamic_address, sa_hdr in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 160, SP - 48); (SA + 8, SA + 24); (P, P + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 160, SP - 48); (SA + 8, SA + 24); (P, P + 8)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 160, SP - 48); (SA + 8, SA + 24); (P, P + 8)]) by sh_fp_lia.
  assert (EU1 : bv_unsigned (Z_to_bv 64 (SP + -48)) = SP + -48) by (apply unsigned_lit; lia).
  assert (EUE : bv_unsigned (Z_to_bv 64 E) = E) by (apply unsigned_lit; lia).
  zstep; th_if_lit. do 3 zstep. zstep.
  tcall (T_set_local_ex_steady_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN k 3 MK SA P 4 pad top (Z_to_bv 64 1) (Z_to_bv 64 (-1)));
    first [reflexivity | eassumption | lia | right; reflexivity | exact (ut_munch _ m _ UT MU HWU) | idtac].
  all: try (eapply acc_munch_sh; [eassumption | exact MU | exact HWS | lia | lia]).
  cbv beta delta [mkR].
  rewrite (eg_sa_delta_nz E HE) in PC1. unfold sa_hdr in PC1. change (Z_to_bv 64 (1 + 0)) with (Z_to_bv 64 1) in PC1.
  zstep; th_if_lit. do 2 zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold eg_w3_post, SITE_eg_icf, e_init_crypto, sa_hdr. apply evt_done. do 5 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside app]; intros; lia|].
  repeat (split; [eassumption|]); eassumption.
Qed.

(* [comment removed for export] *)
Lemma eg_w4 : forall ra0 sp gp tp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo E : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem),
       ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
       /\ munch ([] : list (Z * Z)) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 SITE_eg_icf) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 0)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 E) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_eg_icf) fc None m (seg_rom asegs)).
Proof.
  intros until E. intros ST HLO HLOS SPH FR MI. unfold SITE_eg_icf in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU1 : bv_unsigned (Z_to_bv 64 (SP + -48)) = SP + -48) by (apply unsigned_lit; lia).
  zstep; th_if_lit. zstep.
  do 6 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  apply evt_done. eexists. split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.
