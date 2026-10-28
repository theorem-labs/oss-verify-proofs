(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_T_sk Fz_K_skw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Definition SK_PUSH_ROOM_STACK : Z := 208.
Definition T_sk_push_room_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A D num nalloc s01 : Z) (pad cmpt freet copyt : word) (junk : list byte),
    a0 = Z_to_bv 64 A -> 0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
    rw_cells asegs m A (sk_cells (Z_to_bv 64 num) pad (Z_to_bv 64 D) (Z_to_bv 64 s01) (Z_to_bv 64 nalloc) z64 cmpt freet copyt) -> acc asegs m A 56 ->
    (s01 = 0 \/ s01 = 1) -> 1 <= num -> num + 1 <= nalloc -> 4 <= nalloc < 2 ^ 20 ->
    0x10007fff8000 <= D -> D mod 8 = 0 -> D + 8 * nalloc <= lo -> rw_cells asegs m D [CB (Z.to_nat (8 * nalloc)) junk] -> acc asegs m D (8 * nalloc) ->
    (A + 56 <= D \/ D + 8 * nalloc <= A) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - SK_PUSH_ROOM_STACK -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (num + 1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - SK_PUSH_ROOM_STACK, bv_unsigned sp); (A, A + 56); (D, D + 8 * nalloc)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 (num + 1)) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 nalloc) z64 cmpt freet copyt)
                 /\ rw_cells asegs m' D [CB (Z.to_nat (8 * nalloc)) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_sk_push) fc None m (seg_rom asegs)).

Theorem T_sk_push_room_proof : T_sk_push_room_stmt.
Proof.
  intros until junk. intros -> AHI AAL ALO HC ACC S01 NUM NA NAL DHI DAL DLO DC ACCD DISJ UT SHC ST LO0 LO HTOP MI. unfold SK_PUSH_ROOM_STACK in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HWS : sh_fp [(bv_unsigned sp - 208, bv_unsigned sp); (A, A + 56); (D, D + 8 * nalloc)]%Z) by sh_fp_lia.
  assert (HWU : ut_fp [(bv_unsigned sp - 208, bv_unsigned sp); (A, A + 56); (D, D + 8 * nalloc)]%Z) by ut_fp_lia.
  cl_eu (bv_unsigned sp) (-112) EU1.
  assert (S01R : 0 <= s01 < 2) by lia.
  pose proof (rw_cells_bound _ _ _ _ DC) as DR. cbn [cells_size csize Nat.add] in DR. assert (D0 : D <> 0) by lia. assert (DR' : 0 <= D < 2 ^ 64) by lia.
  (* [comment removed for export] *)
  assert (LATER : forall mx, munch [(bv_unsigned sp - 208, bv_unsigned sp); (A, A + 56); (D, D + 8 * nalloc)]%Z m mx ->
            acc asegs mx A 56 /\ acc asegs mx D (8 * nalloc) /\ img_untouched mx /\ ro_cells asegs mx g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]).
  { intros mx MUx. split; [exact (acc_munch_sh _ m _ _ _ ACC MUx HWS ltac:(lia) ltac:(lia))|]. split; [exact (acc_munch_sh _ m _ _ _ ACCD MUx HWS ltac:(lia) ltac:(lia))|].
    split; [exact (ut_munch _ m _ UT MUx HWU)|].
    eapply ro_cells_transport; [exact SHC| exact MUx|]. unfold g_shadow_memory_dynamic_address. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (skp_w0g ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 F fc m lo A num); try eassumption; lia. }
  intros ms1 (a3x & m1 & -> & MU1 & WM1 & MI1 & ST1 & HC1).
  assert (MU01 : munch [(bv_unsigned sp - 208, bv_unsigned sp); (A, A + 56); (D, D + 8 * nalloc)]%Z m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros; lia).
  destruct (LATER m1 MU01) as (ACC1 & ACCD1 & UT1 & SHC1).
  assert (DC1 : rw_cells asegs m1 D [CB (Z.to_nat (8 * nalloc)) junk]).
  { eapply rw_cells_transport; [exact DC| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (ski_w0g ra sp gp tp t0 t1 t2 s0 s1 _ _ a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 F fc m1 lo A num num); try eassumption; lia. }
  intros ms2 (j & m2 & -> & MU2 & WM2 & MI2 & FR2 & ST2 & HC2).
  pose proof (munch_trans _ _ _ _ MU01 ltac:(eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia)) as MU02.
  pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM02.
  destruct (LATER m2 MU02) as (ACC2 & ACCD2 & UT2 & SHC2).
  assert (DC2 : rw_cells asegs m2 D [CB (Z.to_nat (8 * nalloc)) junk]).
  { eapply rw_cells_transport; [exact DC1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  rewrite EU1 in ST2 || idtac.
  assert (ST2' : stk asegs m2 lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)))) by (rewrite EU1; exact ST2).
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (skr_room (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) _ _ a5 a6 a7 (Z_to_bv 64 num) s3 a1 s5 s6 _ _ _ s10 s11 t3 t4 t5 t6 F fc m2 lo A D num nalloc);
      try eassumption; rewrite ?EU1; try eassumption; lia. }
  cbv beta. intros ms3 (a1' & a2' & a3' & a4' & a5' & m3 & -> & MU3 & WM3 & MI3 & ST3 & HC3). rewrite ?EU1 in MU3. rewrite ?EU1 in ST3.
  rewrite (ret_pc_even SITE_ski_reserve) by (unfold SITE_ski_reserve; lia).
  pose proof (munch_trans _ _ _ _ MU02 ltac:(eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside]; intros; lia)) as MU03.
  pose proof (wmono_trans asegs _ _ _ WM02 WM3) as WM03.
  destruct (LATER m3 MU03) as (ACC3 & ACCD3 & UT3 & SHC3).
  assert (DC3 : rw_cells asegs m3 D [CB (Z.to_nat (8 * nalloc)) junk]).
  { eapply rw_cells_transport; [exact DC2| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -112) [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (ski_w1g sp gp tp t0 t1 t2 a1' a2' a3' a4' a5' a6 a7 s3 s5 s6 s9 s10 s11 t3 t4 t5 t6 a1 F fc m3 lo A D num nalloc s01 pad cmpt freet copyt j junk ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
      try eassumption; lia. }
  cbv beta. intros ms4 (b1 & b2 & b3 & b4 & junk' & m4 & -> & MU4 & WM4 & MI4 & ST4 & HC4 & DC4).
  apply evt_done. do 14 eexists. exists junk', m4. split; [reflexivity|].
  split; [exact (munch_trans _ _ _ _ MU03 ltac:(eapply munch_weaken; [| exact MU4]; unfold sub_fp; cbn [outside]; intros; lia))|].
  split; [exact (wmono_trans asegs _ _ _ WM03 WM4)|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact HC4| exact DC4].
Qed.

Section CKSk.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CRA : crypto_realloc_array_env_stmt RT.

(* [comment removed for export] *)
Definition KG_SITES : list (Z * Z) := [(SITE_ski_reserve, e_sk_insert); (SITE_skr_realloc, e_sk_reserve); (SITE_cr_realloc, e_CRYPTO_realloc)].
Definition KG_CALLS : list (Z * Z) := [(SITE_ski_reserve, e_sk_reserve); (SITE_skr_realloc, e_CRYPTO_realloc_array); (SITE_skr_realloc, e_CRYPTO_realloc); (SITE_cr_realloc, e_realloc)].

(* [comment removed for export] *)
Definition sk_push_grow_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (lb : byte) (canary : word)
    (A D : Z) (pad cmpt freet copyt : word) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (q : Z) (junk' : list byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 5) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 56)] m m'
           /\ cl_env m' lb canary
           /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 5) pad (Z_to_bv 64 q) z64 (Z_to_bv 64 6) z64 cmpt freet copyt)
           /\ rw_cells asegs m' q [CB 48%nat junk']) c
       /\ rt_live RT Σ' = (q, 48) :: live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost 48 /\ 0 < q /\ q mod 16 = 0 /\ q + 48 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ.

Definition T_sk_push_grow_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (A D : Z) (pad cmpt freet copyt : word) (src : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x200 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_sk_push (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> In (bv_unsigned ra, e_sk_insert) (cg_call (rt_cg RT Σ)) ->
  cg_has (rt_cg RT Σ) KG_SITES KG_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  In (A, 56) (rt_live RT Σ) -> A mod 8 = 0 -> In (D, 32) (rt_live RT Σ) ->
  rw_cells asegs m A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 4) z64 cmpt freet copyt) -> rw_cells asegs m D [CB 32%nat src] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sk_push m)))
    (sk_push_grow_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m lb canary A D pad cmpt freet copyt).

(* [comment removed for export] *)
Lemma lv_apart : forall Σ m x y, ART RT Σ m -> In x (rt_live RT Σ) -> In y (rt_live RT Σ) -> x <> y -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof using AF.
  intros Σ m [p1 n1] [p2 n2] HA I1 I2 NE. cbn [fst snd].
  destruct (in_split _ _ I1) as (l1 & l2 & EL).
  assert (I2' : In (p2, n2) (l1 ++ l2)).
  { rewrite EL in I2. apply in_app_or in I2. apply in_or_app. destruct I2 as [X|[X|X]]; [left; exact X| exfalso; exact (NE X)| right; exact X]. }
  exact (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA EL I2').
Qed.

Theorem T_sk_push_grow_proof : T_sk_push_grow_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary A D pad cmpt freet copyt src
    FDO MST -> -> ART0 MI0 CALL HSTK CTX UWC TCALL CGH Hlen Hcr CLE INSA SAAL IND HC DC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 512 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -112). set (usp2 := usp + -192).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 usp2) = usp2) by (apply unsigned_lit; unfold usp2, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 208) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m A 56 ART0 INSA) as (SA0 & SALO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m A 56 ART0 INSA ltac:(lia)) as SAHI.
  pose proof (proj2 (af_acc_live RT AF Σ m A 56 ART0 INSA)) as ACC0.
  pose proof (af_live_range RT AF Σ m D 32 ART0 IND) as (D0 & DLO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m D 32 ART0 IND ltac:(lia)) as DHI.
  pose proof (lv_apart Σ m (A, 56) (D, 32) ART0 INSA IND ltac:(intros E; injection E; lia)) as APAD. cbn [fst snd] in APAD.
  assert (CTXI : cg_ctx (rt_cg RT Σ) e_sk_insert (bv_unsigned ra :: outer)) by (destruct CTX as [_ LK]; split; [exact TCALL| exact LK]).
  (* [comment removed for export] *)
  pose proof (skp_w0g ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 F fc m lo A 4 pad (Z_to_bv 64 D) z64 (Z_to_bv 64 4) z64 cmpt freet copyt
                SAHI SAAL ltac:(clear - SALO LOW; lia) ltac:(lia) HC ACC0 UT SHC ST HLOS ltac:(clear - HLO1; lia) SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a3x & m1 & -> & MU1 & WM1 & MI1 & ST1 & HC1) & Hc1'). clear Hc1. fold usp in MU1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  destruct (af_client_consts RT AF Σ m1 ART1) as (_ & SHC1 & _ & _ & UT1).
  pose proof (proj2 (af_acc_live RT AF Σ m1 A 56 ART1 INSA)) as ACC1.
  (* [comment removed for export] *)
  pose proof (ski_w0g ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.shiftr A 3)) a3x a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 F fc m1 lo A 4 4 pad (Z_to_bv 64 D) z64 (Z_to_bv 64 4) z64 cmpt freet copyt
                SAHI SAAL ltac:(clear - SALO LOW; lia) ltac:(lia) HC1 ACC1 UT1 SHC1 ST1 HLOS ltac:(clear - HLO1; lia) SPH MI1) as W1.
  cl_lift W1 Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (j & m2 & -> & MU2 & WM2 & MI2 & FR2 & ST2 & HC2) & Hc2'). clear Hc2. fold usp in MU2, FR2, ST2, Hc2'. fold usp1 in FR2, ST2, Hc2'.
  pose proof (cl_seg_ART RT AF Σ m1 m2 usp 112 [] ART1 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU2 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM2) as ART2.
  pose proof (cl_seg_pres RT AF Σ m1 m2 usp 112 [] ART1 ltac:(lia) ltac:(lia) MU2) as PR2.
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2) by (intros a Ha; rewrite (PR2 a ltac:(left; exact Ha) I); apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m1 m2 lb canary CLE1 MU2 ltac:(cl_fp_lia)) as CLE2.
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (proj2 (af_acc_live RT AF Σ m2 A 56 ART2 INSA)) as ACC2.
  assert (FRR2 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m2 usp1 [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR2). }
  destruct (cl_chain_call (rt_cg RT Σ) e_sk_insert e_sk_reserve SITE_ski_reserve m m2 ra s0 sp (Z_to_bv 64 usp1) outer CTXI
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG02 FRR2 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  (* [comment removed for export] *)
  pose proof (rw_cells_bound _ _ _ _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
  pose proof (skr_grow_w0 (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 (Z.shiftr A 3)) a3x a5 a6 a7 (Z_to_bv 64 4) s3 a1 s5 s6
               (Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6 F fc m2 lo A D pad z64 cmpt freet copyt
                SAHI SAAL ltac:(clear - SALO LOW; lia) HC2 ACC2 ltac:(clear - D0; lia) ltac:(clear - DR; lia) UT2 SHC2) as W2.
  rewrite EU1 in W2. specialize (W2 ST2 HLOS ltac:(unfold usp1; clear - HLO1; lia) ltac:(unfold usp1; clear - SPH; lia) MI2).
  cl_lift W2 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (j2 & m3 & -> & MU3 & WM3 & MI3 & FR3 & ST3 & HC3) & Hc3'). clear Hc3.
  replace (usp1 + -80) with usp2 in FR3, ST3, Hc3' by (unfold usp1, usp2; lia).
  assert (MU3' : munch ([] ++ [(usp - 208, usp)]) m2 m3) by (eapply munch_weaken; [| exact MU3]; unfold sub_fp, usp1; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m2 m3 usp 208 [] ART2 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU3' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM3) as ART3.
  pose proof (cl_seg_pres RT AF Σ m2 m3 usp 208 [] ART2 ltac:(lia) ltac:(lia) MU3') as PR3.
  assert (AG23 : agree_on (fun x => usp1 <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; cbn [outside]; unfold usp1 in *; lia).
  pose proof (cl_env_seg _ m2 m3 lb canary CLE2 MU3 ltac:(cl_fp_lia)) as CLE3.
  assert (FRR3 : rw_cells asegs m3 (usp1 - 16) [C8 sp; C8 (Z_to_bv 64 SITE_ski_reserve)]).
  { replace (usp1 - 16) with (usp2 + Z.of_nat (cells_size [CB 8 j2; C8 (Z_to_bv 64 (Z.shiftr A 3 + SHB)); C8 s6; C8 s5; C8 a1; C8 s3; C8 (Z_to_bv 64 4); C8 (Z_to_bv 64 A)])) by (cbn [cells_size csize Nat.add]; unfold usp1, usp2; lia).
    exact (rw_cells_skip m3 usp2 [CB 8 j2; C8 (Z_to_bv 64 (Z.shiftr A 3 + SHB)); C8 s6; C8 s5; C8 a1; C8 s3; C8 (Z_to_bv 64 4); C8 (Z_to_bv 64 A)] [C8 sp; C8 (Z_to_bv 64 SITE_ski_reserve)] FR3). }
  pose proof (unsigned_lit SITE_ski_reserve ltac:(unfold SITE_ski_reserve; lia)) as EUS.
  assert (CTX1' : cg_ctx (rt_cg RT Σ) e_sk_reserve (bv_unsigned (Z_to_bv 64 SITE_ski_reserve) :: bv_unsigned ra :: outer)) by (rewrite EUS; exact CTX1).
  assert (AG23' : agree_on (fun x => bv_unsigned (Z_to_bv 64 usp1) <= x < USTACK_TOP) m2 m3) by (rewrite EU1; exact AG23).
  assert (FRR3' : rw_cells asegs m3 (bv_unsigned (Z_to_bv 64 usp1) - 16) [C8 sp; C8 (Z_to_bv 64 SITE_ski_reserve)]) by (rewrite EU1; exact FRR3).
  assert (H16a : bv_unsigned (Z_to_bv 64 usp2) + 16 <= bv_unsigned (Z_to_bv 64 usp1)) by (rewrite EU1, EU2; unfold usp1, usp2; lia).
  assert (H16b : bv_unsigned (Z_to_bv 64 usp1) + 16 <= USTACK_TOP) by (rewrite EU1; unfold usp1, USTACK_TOP in *; lia).
  destruct (cl_chain_call (rt_cg RT Σ) e_sk_reserve e_CRYPTO_realloc SITE_skr_realloc m2 m3 (Z_to_bv 64 SITE_ski_reserve) sp (Z_to_bv 64 usp1) (Z_to_bv 64 usp2) (bv_unsigned ra :: outer)
              CTX1' (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; right; left; reflexivity)) UWC1 AG23' FRR3' H16a H16b) as (CTX2 & UWC2).
  rewrite EUS in CTX2, UWC2.
  (* [comment removed for export] *)
  apply (C_CRA Σ PMc (Z_to_bv 64 SITE_skr_realloc) (Z_to_bv 64 usp2) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 usp1) (Z_to_bv 64 A)
          (Z_to_bv 64 D) (Z_to_bv 64 6) (Z_to_bv 64 8) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 212) (Z_to_bv 64 6) a6 a7
          (Z_to_bv 64 (A + 8)) (Z_to_bv 64 5) (Z_to_bv 64 (A + 20)) (Z_to_bv 64 (Z.shiftr (A + 8) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (A + 20) 3 + SHB)) (Z_to_bv 64 6) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6
           F fc m3 D 32 6 8 lo (SITE_ski_reserve :: bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) IND ltac:(lia) ltac:(lia) ART3 MI3).
  { fold usp in SPA. cl_call_ok EU2 ST3 LOW SPA 12. }
  { rewrite EU2. unfold usp2, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_skr_realloc) by (unfold SITE_skr_realloc; lia). exact CTX2. }
  { exact UWC2. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [KG_SITES KG_CALLS In] in Hx |- *; clear - Hx; tauto. }
  { exact Hlen. } { clear - Hcr. unfold mcost. replace (6 * 8 <=? 64512) with true by reflexivity. lia. } { exact CLE3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & q & Hc4 & LV4 & FRS4 & SP4 & CR4 & Q0 & Q16 & QU & CG4).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & CLE4 & WRQ & ACQ & CPY) & Hc4'). clear Hc4.
  destruct RS4 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F4 & fc4 & ->).
  rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even SITE_skr_realloc) in Hc4' by (unfold SITE_skr_realloc; lia).
  change (6 * 8) with 48 in *.
  (* [comment removed for export] *)
  assert (INA' : In (A, 56) (live_remove D (rt_live RT Σ))) by (apply live_remove_keep; [exact INSA| cbn [fst]; clear - APAD; lia]).
  assert (INA2 : In (A, 56) (rt_live RT Σ2)) by (rewrite LV4; right; exact INA').
  assert (INQ : In (q, 48) (rt_live RT Σ2)) by (rewrite LV4; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m4 q 48 ART4 INQ) as (_ & QLO & _). rewrite SP4 in QLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 q 48 ART4 INQ ltac:(lia)) as QHI.
  pose proof (wg_live_apart RT AF Σ2 m4 [] q 48 (live_remove D (rt_live RT Σ)) A 56 ART4 LV4 INA') as AQP.
  assert (AG34 : forall a k, usp2 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4. left. lia. }
  assert (FR4 : rw_cells asegs m4 usp2 [CB 8 j2; C8 (Z_to_bv 64 (Z.shiftr A 3 + SHB)); C8 s6; C8 s5; C8 a1; C8 s3; C8 (Z_to_bv 64 4); C8 (Z_to_bv 64 A); C8 sp; C8 (Z_to_bv 64 SITE_ski_reserve)]).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FR3). apply AG34; cbn [cells_size csize Nat.add]; unfold usp2, USTACK_TOP in *; lia. }
  assert (FR24 : rw_cells asegs m4 usp1 [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ FR2). eapply agree_trans; [| apply AG34; cbn [cells_size csize Nat.add]; unfold usp1, usp2, USTACK_TOP in *; lia].
    eapply agree_sub; [exact AG23|]. cbv beta. cbn [cells_size csize Nat.add]. intros x Hx. unfold usp1, USTACK_TOP in *. lia. }
  assert (HC4 : rw_cells asegs m4 A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 4) z64 cmpt freet copyt)).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ HC3). intros x Hx. cbv beta in Hx. unfold sk_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES4. right; right; left. exists A, 56. split; [exact INA'| lia]. }
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (proj2 (af_acc_live RT AF Σ2 m4 A 56 ART4 INA2)) as ACC4.
  (* [comment removed for export] *)
  pose proof (skr_grow_w1 (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 SHB) s9 s10 s11 u3 u4 u5 u6 F4 fc4 m4 lo A D q pad z64 cmpt freet copyt j2
               (Z_to_bv 64 SITE_ski_reserve) sp (Z_to_bv 64 A) (Z_to_bv 64 4) s3 a1 s5 s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB))
                SAHI SAAL ltac:(clear - SALO LOW; lia) HC4 ACC4 ltac:(clear - Q0 QU; unfold USTACK_TOP in *; lia) UT4 SHC4) as W3.
  rewrite EU1 in W3. replace (usp1 + -80) with usp2 in W3 by (unfold usp1, usp2; lia).
  specialize (W3 FR4 ST4 HLOS ltac:(unfold usp1; clear - HLO1; lia) ltac:(unfold usp1; clear - SPH; lia) MI4).
  cl_lift W3 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (e1 & m5 & -> & MU5 & WM5 & MI5 & ST5 & HC5) & Hc5'). clear Hc5.
  rewrite (ret_pc_even SITE_ski_reserve) in Hc5' by (unfold SITE_ski_reserve; lia).
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 usp2 ART4 ltac:(rewrite SP4; unfold usp2; lia)); [| exact WM5]. intros x Hx. apply MU5. cbn [outside].
    split; [| split; [| exact I]]. all: intros X; apply Hx; right; right; left; exists A, 56; split; [exact INA2| lia]. }
  assert (FR25 : rw_cells asegs m5 usp1 [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR24| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize Nat.add]. unfold usp1. clear - SALO LOW HLO1. lia. }
  destruct (af_client_consts RT AF Σ2 m5 ART5) as (_ & SHC5 & _ & _ & UT5).
  pose proof (proj2 (af_acc_live RT AF Σ2 m5 A 56 ART5 INA2)) as ACC5.
  pose proof (proj2 (af_acc_live RT AF Σ2 m5 q 48 ART5 INQ)) as ACCQ5.
  destruct (wr_at_rw_CB m5 q 48 (wr_at_transport asegs m4 m5 q 48 WRQ WM5) ltac:(lia)) as (jq & NQ). change (Z.to_nat 48) with 48%nat in NQ.
  (* [comment removed for export] *)
  pose proof (ski_w1g sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 e1 b2 b3 b4 b5 b6 b7 s3 s5 s6 s9 s10 s11 u3 u4 u5 u6 a1 F4 fc4 m5 lo A q 4 6 0 pad cmpt freet copyt j jq
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                SAHI SAAL ltac:(clear - SALO LOW; lia) HC5 ACC5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(left; reflexivity) QHI ltac:(clear - Q16; Z.div_mod_to_equations; lia)
                ltac:(clear - QLO LOW; lia) NQ ACCQ5 ltac:(clear - AQP; lia) UT5 SHC5) as W4.
  fold usp in W4. fold usp1 in W4.
  specialize (W4 FR25 ST5 HLOS ltac:(clear - HLO1; lia) SPH MI5).
  cl_lift W4 Hc5' c6 Hc6.
  change (4 + 1) with 5 in Hc6. change (8 * 6) with 48 in Hc6. change (Z.to_nat 48) with 48%nat in Hc6.
  (* [comment removed for export] *)
  assert (QOFF : forall a, aclient (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (q <= a < q + 48)).
  { intros a Ha. pose proof (af_live_range RT AF Σ2 m4 q 48 ART4 INQ) as (R0 & R1 & R2). rewrite SP4 in R1.
    destruct Ha as [H|[H|[H|[H|H]]]].
    - clear - H R1 NUM. lia.
    - pose proof (client_static_range a H). unfold SEGTOP_A in *. clear - H0 QHI. lia.
    - destruct H as (p2 & n2 & Hin & Hp). pose proof (wg_live_apart RT AF Σ2 m4 [] q 48 (live_remove D (rt_live RT Σ)) p2 n2 ART4 LV4 Hin). clear - H Hp. lia.
    - destruct H as (f & k & Hin & Hf). rewrite <- FRS4 in Hin. pose proof (af_frames_range RT AF Σ2 m4 f k ART4 Hin) as (_ & _ & _ & R3). destruct (R3 q 48 INQ); clear - H Hf; lia.
    - destruct H as (f & k & Hin & Hf). rewrite <- FRS4 in Hin. pose proof (af_fshadow_apart RT AF Σ2 m4 f k ART4 Hin) as (SL & _). destruct (SL q 48 INQ); clear - H Hf; lia. }
  apply Hk.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (e1' & e2' & e3' & e4' & junk' & m6 & -> & MU6 & WM6 & MI6 & ST6 & HC6 & NQ6) & Hc6'). clear Hc6.
  exists Σ2, q, junk'.
  split.
  { apply (ASTA_conseq RT Σ2 PMc _ _ c6 Hc6'). intros ms <-. exists m6.
    split; [exists u0, u1, u2, e1', e2', e3', e4', b5, b6, b7, u3, u4, u5, u6, F4, fc4; reflexivity|].
    assert (ART6 : ART RT Σ2 m6).
    { apply (af_frame RT AF Σ2 m5 m6 usp ART5 ltac:(rewrite SP4; lia)); [| exact WM6]. intros x Hx. apply MU6. cbn [outside].
      split; [| split; [| split; [| exact I]]]; intros X; apply Hx; right; right; left.
      - exists A, 56. split; [exact INA2| lia].
      - exists A, 56. split; [exact INA2| lia].
      - exists q, 48. split; [exact INQ| lia]. }
    split; [exact (conj ART6 (conj MI6 ST6))|].
    split.
    { intros a Ha Ho. cbn [outside] in Ho. destruct Ho as [O1 _].
      assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (live_remove_sub _ _ _ He)| intros e He; exact He| lia]).
      assert (SPL : usp <= bv_unsigned a \/ bv_unsigned a < usp - 512) by exact (cl_split RT AF Σ m usp 512 _ ART0 ltac:(lia) ltac:(lia) Ha0).
      rewrite (MU6 a) by (cbn [outside]; split; [clear - O1; lia| split; [clear - O1; lia| split; [exact (QOFF _ Ha)| exact I]]]).
      rewrite (MU5 a) by (cbn [outside]; split; [clear - O1; lia| split; [clear - O1; lia| exact I]]).
      rewrite (PRES4 a) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| unfold usp2; lia]).
      rewrite (MU3 a) by (cbn [outside]; unfold usp1; split; [clear - SPL; lia| exact I]).
      rewrite (PR2 a Ha0 I). exact (PR1 a Ha0 I). }
    split; [| exact (conj HC6 NQ6)].
    apply (cl_env_seg _ m5 m6 _ canary ltac:(apply (cl_env_seg _ m4 m5 _ canary CLE4 MU5); cl_fp_lia) MU6). cl_fp_lia. }
  split; [exact LV4|]. split; [exact FRS4|]. split; [exact SP4|]. split; [exact CR4|]. split; [exact Q0|]. split; [exact Q16|]. split; [exact QU| exact CG4].
Qed.
End CKSk.
