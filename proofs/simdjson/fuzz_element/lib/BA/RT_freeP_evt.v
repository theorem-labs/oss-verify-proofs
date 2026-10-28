(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit I_lkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_asan_defs R_deallocate R_qput R_asan_free R_prim_kit R_depot_unwind RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_malstate RT_freelift RT_fkit RT_freestate RT_freeA RT_freeA2 RT_geo0 RT_freeS RT_drain_kit RT_freeSA RT_freeSA2 RT_freeSL1 RT_freeSL2 RT_freeSL3 R_unwind_gen RT_gentrace RT_freeP_defs RT_freeP_runA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Definition segP_post (Σ : rtsA) (k : nat) (s : secst) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (tr : list Z) (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 0x5faec) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
                 (Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (bv_unsigned sp + -2208)) (Z_to_bv 64 (s_mb s + 6128)) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 0x82fc0) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x5d978) fc None m' (seg_rom asegs)
    /\ ARTcK (pass_d Σ k s (fst (depot_put (dep Σ) tr))) k m'
    /\ schunkP k s m'
    /\ (tr_ok tr /\ (1 <= length tr <= 30)%nat)
    /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rt_pres (live_remove (s_ubeg s) (live Σ)) (frames Σ) (bv_unsigned sp) m m'
    /\ icpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
    /\ qput_frame m' (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x83030)
         (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 (s_mb s + 6128 + 16)) (Z_to_bv 64 0x82fc0) (Z_to_bv 64 1)
         (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6.

Theorem segP_evt : forall (Σ : rtsA) (k : nat) (s : secst)
    (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  ART_A Σ m -> mem_inv asegs m -> call_ok RTA Σ m sp lo -> unwind_ok ra s0 sp ->
  nth_error (sec Σ) k = Some s -> s_quar s = false -> 0x10000000 < s_n s ->
  evt asegs (segP_post Σ k s ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (entry_st ra sp gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 (Z_to_bv 64 (s_ubeg s)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m).
Proof.
  intros Σ k s ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ART0 MI0 CALL UWOK Hk Hq Hbig.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & _ & _ & AI & MCS & _ & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  destruct CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (ss_geo Σ m k s ART0 Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
  destruct (ART_ia Σ m ART0) as (b & IS).
  destruct (art_trace_main Σ m free_pc ra s0 sp ART0 ltac:(unfold l_ACEIL, RT_STACK in *; lia) UWOK ltac:(unfold free_pc; lia))
    as (ch & tr & CHC & TR & Htr1 & Htr2).
  assert (Htr : tr_ok tr /\ (1 <= length tr <= 30)%nat) by (split; [exact Htr1 | exact Htr2]).
  clear Htr1 Htr2.
  eapply evt_cut.
  { apply (free_pre_spec ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (s_ubeg s) (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo b ch tr);
      try assumption.
    all: try (unfold s_ubeg; clear - K7 K8 K15 K16 K17 K33; lia).
    all: try (clear - LOR; unfold RT_STACK in *; lia).
    all: try (clear - SPT; unfold USTACK_TOP in *; lia).
    all: try (clear - Hbt; lia). all: try (clear - Htop; lia). all: try (clear - HT; unfold img_hull_lo, img_hull_hi, SEGTOP_A in *; lia).
    all: try (pose proof (sr_tcx Σ m ART0) as (_ & _ & _ & _ & X5 & _); clear - X5; unfold SEGTOP_A in *; lia). }
  intros ms1 P1.
  destruct P1 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & tb & jp & m1 & -> & MU1 & WM1 & MI1 & IS1 & FRs & FRp & FRt & TB & HTB & FRb & TB1 & ST1).
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
  assert (Hsp' : l_ACEIL (lay Σ) + 0xF000 <= usp) by (clear - Hsp; lia).
  pose proof (fn_ART Σ m usp ART0 Hsp' m1 MU1 WM1 IS1 TB1) as ART1.
  replace (s_ubeg s) with (s_mb s + 6128 + 16) by (unfold s_ubeg; clear; lia).
  assert (Husp : usp + 16 <= USTACK_TOP) by (clear - SPT; unfold USTACK_TOP in *; lia).
  assert (HLO' : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL in *; lia).
  assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
  eapply evt_mono.
  { destruct K10 as [HL|HH].
    - exact (segP_run_L Σ m1 k s usp lo tr tb ART1 Hk Hq Hbig Hsp Husp HLO' HLO2 ST1 MI1 FRb TB HTB Htr HL
               gp x0 x1 x2 x3 x4 s6 s7 s8 s9 s10 s11 x5 x6 x7 x8 F fc).
    - exact (segP_run_H Σ m1 k s usp lo tr tb ART1 Hk Hq Hbig Hsp Husp HLO' HLO2 ST1 MI1 FRb TB HTB Htr HH
               gp x0 x1 x2 x3 x4 s6 s7 s8 s9 s10 s11 x5 x6 x7 x8 F fc). }
  intros ms P. destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & m' & -> & ART' & CK' & MI' & WM' & MW' & ST' & FR').
  unfold segP_post. exists tr, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, m'. split; [reflexivity|].
  split; [exact ART'|]. split; [exact CK'|].
  split; [exact Htr|]. split; [exact MI'|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')|]. split; [exact ST'|]. split.
  { intros a Ha. rewrite (MW' a (ss_client Σ m1 k s usp ART1 Hk Hsp _ Ha)).
    exact (MU1 a (fn_client Σ m usp ART0 Hsp' _ (aclient_live_remove _ _ _ _ _ Ha))). }
  split; [|exact FR'].
  apply (icpt_frame_transport (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (s_mb s + 6128) (s_n s) usp)
           m1 m' usp ra s0 s1 s2 s3 s4 s5); [| exact MW' | exact WM' |].
  - split; [exact FRs|]. split; [exists jp; exact FRp|]. split; [exact FRt|]. split; [exists (wr_trace tr tb); split; [exact TB|]|].
    + rewrite wr_trace_length; [exact HTB|]. rewrite HTB. destruct Htr as (_ & Htl5); lia.
    + exists (Z_to_bv 64 (Z.of_nat (length tr))). exact FRb.
  - unfold W_A1. cbn [disjoint_from].
    clear - K8 K15 K16 K17 K18 K21 K22 K23 K25 K28 K31 K32 Hsp. unfold SHB in *. repeat split; try exact I; lia.
Qed.

End GWIN.
