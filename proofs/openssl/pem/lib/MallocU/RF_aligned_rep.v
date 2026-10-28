(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry MallocKit_A MallocBlocks MallocFacts_B MallocFacts_inv MallocReframe.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl MI_Inv MI_Read MI_Geom MI_Pres2 MI_WFree.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_A RF_get_meta
  RF_realloc_frame RF_realloc_rep RF_aligned_frame RF_aligned_head RF_aligned_arms RMalloc_reframe.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma rpres_move : forall (Cfp : Z -> Prop) m0 m S P' E n k q' off',
  rpres_except Cfp m0 m -> 16 <= S -> S + 16 <= P' -> 0 <= n -> P' + n <= E -> E + 5 <= 2^64 ->
  (forall x, S - 3 <= x < E -> ~ (P' <= x < P' + n) -> Cfp x) ->
  rpres_except Cfp m0 (ra_move_mem m S P' E n k q' off').
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Cfp m0 m S P' E n k q' off' HP S16 SP N0 PE EHI HC.
  assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
  unfold ra_move_mem. cbv zeta.
  apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros x Hx; apply HC; lia].
  apply rpres_write; [| lia | cbn; lia | cbn; intros x Hx; apply HC; lia].
  apply rpres_setsize; [| lia | lia | lia | lia | intros x Hx NX; apply HC; [lia| exact NX]].
  apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros x Hx; apply HC; lia].
  apply rpres_write; [| lia | cbn; lia | cbn; intros x Hx; apply HC; lia].
  apply rpres_write; [exact HP | lia | cbn; lia | cbn; intros x Hx; apply HC; lia].
Qed.

Section REP.
Variables (st : mstate) (LB : list block).
Variables (c : cptr) (off n0 : Z) (g bg : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis C : CINV st LB.
Hypothesis BF : blk_facts st c off n0 g bg i ai a ar ka.
Hypothesis INI : c_init_done (ctx st) <> 0.

Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let cz := snd bg + 16 + stride * i.
Let po := snd bg + 16 + stride * i + 16 * off.
Let eo := snd bg + 16 + stride * i + stride - 4.
Let q := (po - snd bg - 16) / 16.

(* [comment removed for export] *)
Lemma raligned_head_bf : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r len,
  rmrep st m -> mem_inv usegs m -> (s_regions st) !! (fst bg) = Some r ->
  s0 = Z_to_bv 64 64 -> s1 = Z_to_bv 64 len ->
  bv_unsigned a0 = r_base r + po -> m_sizeclass mr < 48 -> stride < 2^20 ->
  evt usegs (rah_post ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 F fc m i len (r_base r + snd bg) stride (r_base r + po))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b24cc) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until len. intros MRm MI Hr HS0 HS1 HP SC48 ST20.
  destruct (rrb_geo st LB c off n0 g bg i ai a ar ka C BF) as (r' & Hr' & Kr & B0 & S16 & SI0 & Hi & OFF & N0 & SPAN & FIT & O16 & RES0 & Ec & PM & Q1 & Q2).
  rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  fold mr in S16, SI0, SPAN, FIT, O16, Ec, PM, Q1, Q2. fold stride in S16, SI0, SPAN, FIT, O16, Ec, PM, Q1, Q2.
  pose proof (ci_gmetas _ _ C bg g (rrb_hosts st c off n0 g bg i ai a ar ka BF)) as GO.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  rewrite (gbase_bm st c off n0 g bg i ai a ar ka BF) in SH. rewrite Ec in SH. cbn [fst snd] in SH.
  change (MR st g) with mr in SH. fold stride in SH. unfold UNIT, IB in SH.
  replace (snd bg + 16 + stride * i + 16 * off) with po in SH by reflexivity.
  replace ((po - snd bg - 16) / 16) with q in SH by reflexivity.
  destruct SH as (K4 & K3 & K2 & K1 & _). unfold known in K4, K3, K2, K1. cbn [fst snd] in K4, K3, K2, K1.
  set (res := snd bg + 16 + stride * i + stride - 4 - po - n0) in *.
  pose proof (u16_bytes q Q2) as U16.
  assert (RES0' : 0 <= res) by (unfold res, po; lia).
  assert (EIDX : Z.land (i + 32 * Z.min res 5) 31 = i) by (apply land31_idx; lia).
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em).
  pose proof (blk_meta_guards st c off n0 g bg i ai a ar ka BF) as GU. cbv zeta in GU.
  rewrite Ec in GU. cbn [snd] in GU. change (MR st g) with mr in GU. fold stride in GU. unfold UNIT in GU.
  replace ((snd bg + 16 + stride * i + 16 * off - snd bg - 16) / 16) with q in GU by reflexivity.
  destruct GU as (_ & _ & G16 & G63 & G17).
  pose proof MRm as (WF & CX & GL & AR & GR & SHR).
  destruct WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst bg) r Hr) as (RB0 & BAL & L0 & BC & _).
  assert (POR : 16 <= po /\ po + 16 <= round_up_pg (r_len r)) by (unfold po; clear - B0 SI0 OFF SPAN O16; lia).
  (* [comment removed for export] *)
  destruct (rmrep_shadow_read st m (fst bg) r (po - 4) 0 MRm Hr Kr ltac:(lia) K4) as [R4 _].
  destruct (rmrep_shadow_read st m (fst bg) r (po - 3) (i + 32 * Z.min res 5) MRm Hr Kr ltac:(lia) K3) as [R3 B3].
  destruct (rmrep_shadow_read2 st m (fst bg) r (po - 2) (byte_of q 0) (byte_of q 1) MRm Hr Kr ltac:(lia) ltac:(lia) K2 ltac:(replace (po - 2 + 1) with (po - 1) by lia; exact K1)) as (R2 & LO & HI).
  rewrite <- le2_lohi in R2 by lia. rewrite U16 in R2.
  (* [comment removed for export] *)
  destruct (rmrep_group_read st m bg (mkGhdr (Some g) ai) MRm (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as [RG _]. cbn [g_meta pw oconc] in RG.
  pose proof (rmrep_meta_chunk st m g MRm (go_slot _ _ _ GO)) as MM. fold mr in MM. unfold meta_cells in MM. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) in MM. cbn [pw oconc] in MM.
  assert (Har : (s_areas st) !! (area_of g) = Some ar) by (rewrite Em, (area_of_mslot a ka Hal Hka); exact Ha).
  pose proof (rmrep_area_check_read st m (area_of g) ar MRm Har) as RA. rewrite Hck in RA.
  pose proof (rmrep_ctx_secret_read st m MRm) as RC. rewrite (rsec_init _ _ INI) in RC.
  rewrite <- (wz_mod64 (c_secret (ctx st) + bv_unsigned rr_secret)) in RA, RC.
  (* [comment removed for export] *)
  assert (HB : conc st bg = r_base r + snd bg) by (apply conc_region'; exact Hr).
  destruct (go_slot _ _ _ GO) as (a' & ara & k' & Ha' & Hkk & Eg).
  destruct (WA a' ara Ha') as (rg & Hrg & A0 & A1 & AAL & ANG & _).
  assert (HG : conc st g = r_base rg + snd a' + (AREA_HDR + META_SIZE * k')).
  { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a' rg Hrg). reflexivity. }
  destruct (WR (fst a') rg Hrg) as (RGB0 & RGBAL & RGL0 & RGBC & _).
  assert (Hm : (r_base rg + snd a' + (AREA_HDR + META_SIZE * k')) mod 4096 = AREA_HDR + META_SIZE * k').
  { unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (r_base rg + snd a' + (24 + 40 * k')) with ((24 + 40 * k') + (snd a' / 4096 + r_base rg / 4096) * 4096) by (clear - AAL RGBAL; Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by (clear; lia). apply Z.mod_small. clear - Hkk. lia. }
  assert (HA : conc st (area_of g) = conc st g - conc st g mod 4096).
  { rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a') _ rg Hrg).
    replace ((snd a' + (AREA_HDR + META_SIZE * k')) mod 4096) with (AREA_HDR + META_SIZE * k'); [clear; lia|].
    unfold AREA_HDR, META_SIZE, NSLOTS in *.
    replace (snd a' + (24 + 40 * k')) with ((24 + 40 * k') + (snd a' / 4096) * 4096) by (clear - AAL; Z.div_mod_to_equations; nia).
    rewrite Z.mod_add by (clear; lia). symmetry. apply Z.mod_small. clear - Hkk. lia. }
  assert (P16' : (r_base r + po) mod 16 = 0) by (clear - BAL PM; Z.div_mod_to_equations; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  assert (SCR : 0 <= m_sizeclass mr < 48) by (destruct (go_sc _ _ _ GO) as [X|(X & _)]; fold mr in X; clear - X SC48; lia).
  eapply evt_mono.
  { eapply (raligned_head_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (r_base r + po) (conc st g) (r_base r + snd bg) (conc st (area_of g)) len (i + 32 * Z.min res 5) q (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) ((c_secret (ctx st) + bv_unsigned rr_secret) mod 2^64)
              (pw st (m_prev mr)) (pw st (m_next mr)));
      try (change (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - 16 else 16 * size_class (m_sizeclass mr)) with stride);
      rewrite ?EIDX.
    - exact HS0.
    - exact HS1.
    - exact HP.
    - unfold ceil_window in *. clear - POR RB0. lia.
    - exact P16'.
    - unfold po in *. clear - Q1 B0 RB0. lia.
    - unfold ceil_window in *. clear - POR BC RUP CEIL_RANGE__. lia.
    - unfold po in *. clear - Q1. lia.
    - exact HA.
    - rewrite HG. unfold AREA_HDR, META_SIZE in *. clear - RGB0 A0 Hkk. lia.
    - rewrite HG. unfold ceil_window, AREA_HDR, META_SIZE, NSLOTS in *. pose proof (round_up_pg_ge (r_len rg)) as RUG. clear - RGBC A1 Hkk RUG CEIL_RANGE__. lia.
    - replace (r_base r + po - 4) with (r_base r + (po - 4)) by lia. exact R4.
    - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact R3.
    - replace (r_base r + po - 2) with (r_base r + (po - 2)) by lia. exact R2.
    - rewrite <- HB. exact RG.
    - rewrite <- HB. exact MM.
    - exact RA.
    - exact RC.
    - apply rsize_classes_read; [exact MI | lia].
    - exact B3.
    - exact Q2.
    - exact (go_avail _ _ _ GO).
    - exact (go_freed _ _ _ GO).
    - apply rsec_range.
    - pose proof (go_li _ _ _ GO) as X. fold mr in X. clear - X. lia.
    - rewrite (go_freeable _ _ _ GO). clear. lia.
    - exact SCR.
    - pose proof (go_maplen _ _ _ GO) as X. fold mr in X. clear - X. lia.
    - pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as X. change (MR st g) with mr in X. clear - X. lia.
    - exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF).
    - exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF).
    - exact (G16 SC48).
    - exact G17.
    - clear - S16 ST20. lia.
    - clear - B0 RB0. lia.
    - unfold ceil_window in *. clear - SPAN BC RUP CEIL_RANGE__ RB0 SI0 S16. lia. }
  intros ms' PO. cbv zeta in PO.
  change (if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0) then m_maplen mr * 4096 - 16 else 16 * size_class (m_sizeclass mr)) with stride in PO.
  rewrite EIDX in PO. exact PO.
Qed.

(* [comment removed for export] *)
Definition raligned_ret_rep (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo len A' : Z) (st' : mstate) (r : region) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ rmrep st' m' /\ ticks_ok st' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rpres_except (fun x => r_base r + cz - 3 <= x < r_base r + eo /\ ~ (A' <= x < A' + len)) m m'.

Theorem raligned_tail_rep : forall x1 ra sp gp tp t0 t1 t2 s0 s1 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo r len j8,
  rmrep st m -> mem_inv usegs m -> (s_regions st) !! (fst bg) = Some r ->
  q0 = Z_to_bv 64 64 -> q1 = Z_to_bv 64 len -> a0 = Z_to_bv 64 (r_base r + po) ->
  n0 = len + 48 -> 0 <= len ->
  m_sizeclass mr < 48 -> stride * (m_last_idx mr + 1) < 2^20 -> off <= 255 ->
  (forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst bg ->
     snd b' + 9 <= snd bg + 16 + stride * i - 4 \/ snd bg + 16 + stride * i + stride - 4 <= snd b') ->
  rw_cells usegs m (bv_unsigned sp + -32) (ra_frame j8 ra s0 s1) ->
  stk usegs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 ->
  let P := r_base r + po in
  let adj := 64 - P mod 64 in
  evt usegs (fun ms' =>
       (P mod 64 = 0 /\ raligned_ret_rep ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo len P (rf_setsize_st st c g bg i off len) r m ms')
    \/ (P mod 64 <> 0 /\ raligned_ret_rep ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo len (P + adj)
                           (rf_move_st st c g bg i (off + adj / 16) len) r m ms'))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b24cc) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until j8. intros MRm MI Hr HQ0 HQ1 HA0 EN0 LEN0 SC48 SCNT OFF255 NOGRP FR ST LO SLO P adj.
  destruct (rrb_geo st LB c off n0 g bg i ai a ar ka C BF) as (r' & Hr' & Kr & B0 & S16 & SI0 & Hi & OFF & N0 & SPAN & FIT & O16 & RES0 & Ec & PM & Q1 & Q2).
  rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  fold mr in S16, SI0, SPAN, FIT, O16, RES0, Ec, PM, Q1, Q2. fold stride in S16, SI0, SPAN, FIT, O16, RES0, Ec, PM, Q1, Q2.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as [I0 I1]. change (MR st g) with mr in I1.
  assert (ST20 : stride < 2^20) by (clear - SCNT S16 I0 I1; nia).
  assert (SIC : stride * (i + 1) <= stride * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; [clear - S16; lia| clear - I1; lia]).
  pose proof MRm as (WF & _ & _ & _ & _ & SHR). pose proof WF as (_ & WR & _).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (PR : 0 <= P < 2^64) by (unfold P, po, ceil_window in *; clear - B0 SI0 OFF SPAN O16 RB0 RBC RUP CEIL_RANGE__; lia).
  assert (HP : bv_unsigned a0 = P) by (rewrite HA0; apply unsigned_lit; exact PR).
  set (B := r_base r + snd bg). set (E := r_base r + eo).
  assert (EE : B + 16 + stride * (i + 1) + -4 = E) by (unfold B, E, eo; clear; lia).
  assert (EE4 : B + 16 + stride * (i + 1) = E + 4) by (unfold B, E, eo; clear; lia).
  destruct (SHR _ r Hr Kr) as [WRr HBr].
  (* [comment removed for export] *)
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  rewrite Ec in SH. cbn [fst snd] in SH. change (MR st g) with mr in SH. fold stride in SH. unfold UNIT, IB in SH.
  replace (snd bg + 16 + stride * i + 16 * off) with po in SH by reflexivity.
  destruct SH as (_ & K3 & _). unfold known in K3. cbn [fst snd] in K3.
  set (b3 := i + 32 * Z.min (snd bg + 16 + stride * i + stride - 4 - po - n0) 5) in *.
  assert (B3R : 0 <= b3 < 256) by (unfold b3, po in *; clear - Hi RES0; lia).
  assert (EIDX : Z.land b3 31 = i) by (apply land31_idx; [clear - Hi; lia| unfold po in *; clear - RES0; lia]).
  assert (POR : 16 <= po /\ po + 16 <= round_up_pg (r_len r)) by (unfold po; clear - B0 SI0 OFF SPAN O16; lia).
  destruct (HBr (po - 3) b3 ltac:(clear - POR; lia) K3) as [BK3 _].
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (raligned_head_bf x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r len);
      [exact MRm| exact MI| exact Hr| exact HQ0| exact HQ1| exact HP| exact SC48| exact ST20]. }
  intros ms1 (y5 & y6 & y7 & y28 & [(PM0 & ->)|(PM1 & ->)]).
  - (* [comment removed for export] *)
    unfold rah_regs. fold B. rewrite EE, EE4.
    eapply evt_cut.
    { eapply (raligned_same_walk x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp y5 y6 y7 (Z_to_bv 64 63) q1 a0 (wz i) (wz (B + 16)) (wz stride) (wz 0)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6 F fc m P E len b3).
      - exact HP.
      - exact MI.
      - eapply wr_at_sub; [exact WRr| unfold P; clear - POR; lia| unfold P, E, eo, po in *; clear - SPAN; lia].
      - unfold P. replace (r_base r + po - 3) with (r_base r + (po - 3)) by (clear; lia). exact BK3.
      - exact B3R.
      - unfold E, eo, ceil_window in *. clear - SPAN RBC RB0 RUP CEIL_RANGE__. lia.
      - unfold P. clear - POR RB0. lia.
      - exact LEN0.
      - unfold P, E, eo, po in *. clear - FIT EN0 LEN0. lia.
      - unfold P, E, eo, po in *. clear - ST20 OFF LEN0. lia. }
    intros ms2 (z5 & z6 & z7 & z8 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & m2 & -> & Em2 & MI2).
    rewrite EIDX in Em2.
    set (Cfp := fun x => r_base r + cz - 3 <= x < E /\ ~ (P <= x < P + len)).
    assert (PE2 : rpres_except Cfp m m2).
    { rewrite Em2. apply rpres_setsize; [apply rpres_except_refl| unfold P; clear - POR RB0; lia| exact LEN0| unfold P, E, eo, po in *; clear - FIT EN0 LEN0; lia
                                        | unfold E, eo, ceil_window in *; clear - SPAN RBC RB0 RUP CEIL_RANGE__; lia|].
      intros x Hx NX. split; [unfold P, po, cz in *; clear - Hx OFF; lia| exact NX]. }
    assert (HIGH : forall x, alloc_ceiling <= x -> ~ Cfp x) by (intros x Hx [X _]; unfold E, eo in *; clear - X Hx SPAN RBC; lia).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) (ra_frame j8 ra s0 s1)).
    { eapply rpres_except_rw_cells; [exact PE2| exact FR|]. intros x Hx. apply HIGH. clear - Hx LO SLO. lia. }
    assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -32)).
    { eapply rpres_except_stk; [exact PE2| exact ST|]. intros x Hx. apply HIGH. clear - Hx LO. lia. }
    eapply evt_cut.
    { eapply (raligned_epilogue x1 ra sp gp tp z5 z6 z7 s0 s1 z8 q1 a0 z11 z12 z13 z14 z15 z16 z17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 t4 t5 t6 F fc m2 lo j8);
        [exact FR2| exact ST2| exact SLO| exact MI2]. }
    intros ms3 (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & -> & ST3).
    apply evt_done. left. split; [exact PM0|]. unfold raligned_ret_rep.
    exists u5, u6, u7, u11, u12, u13, u14, u15, u16, u17, u28, u29, u30, u31, m2.
    split; [rewrite HA0; reflexivity|].
    pose proof (rsetsize_mrep st m g bg r i MRm (ci_ticks _ _ C) (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) Hr Kr B0 ltac:(clear - Hi; lia)
                  ltac:(fold mr; fold stride; clear - SPAN; lia) ltac:(fold mr; fold stride; exact S16)
                  ltac:(fold mr; fold stride; exact NOGRP) off len ltac:(clear - OFF; lia) LEN0 ltac:(fold mr; fold stride; clear - FIT EN0 LEN0; lia)
                  ltac:(fold mr; fold stride; clear - ST20 LEN0; lia)) as [MR2 TK2].
    fold mr in MR2, TK2. fold stride in MR2, TK2. rewrite <- Ec in MR2, TK2.
    replace (snd bg + 16 + stride * i + 16 * off) with po in MR2 by reflexivity.
    replace (snd bg + 16 + stride * i + stride - 4) with eo in MR2 by reflexivity.
    fold P in MR2. fold E in MR2. rewrite <- Em2 in MR2.
    split; [exact MR2|]. split; [exact TK2|]. split; [exact MI2|]. split; [exact ST3| exact PE2].
  - (* [comment removed for export] *)
    unfold rah_regs. fold B. rewrite EE, EE4. fold adj.
    assert (ADJ : (adj = 16 \/ adj = 32 \/ adj = 48) /\ adj = 16 * (adj / 16)).
    { assert (P16 : P mod 16 = 0) by (unfold P; clear - RBAL PM; Z.div_mod_to_equations; lia).
      unfold adj. clear - P16 PM1. Z.div_mod_to_equations. lia. }
    destruct ADJ as [ADJ3 ADJE]. set (d := adj / 16) in *.
    assert (DR : 1 <= d <= 3) by (clear - ADJ3 ADJE; lia).
    assert (FIT' : 16 * (off + d) + len + 4 <= stride) by (clear - FIT EN0 DR; lia).
    assert (SEQ : B + 16 + stride * i = r_base r + cz) by (unfold B, cz; clear; lia).
    assert (QR' : 0 <= (cz + 16 * (off + d) - snd bg - 16) / 16 < 65536).
    { replace (cz + 16 * (off + d) - snd bg - 16) with ((stride * i / 16 + off + d) * 16).
      2:{ unfold cz. clear - Q1. assert (stride * i = 16 * (stride * i / 16)) by (Z.div_mod_to_equations; lia). lia. }
      rewrite Z.div_mul by (clear; lia).
      assert (X : 16 * (stride * i / 16 + off + d) < 2^20).
      { assert (stride * i = 16 * (stride * i / 16)) by (clear - Q1; Z.div_mod_to_equations; lia).
        clear - H FIT' LEN0 SIC SCNT. lia. }
      clear - X SI0 OFF DR. split; [apply Z.add_nonneg_nonneg; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]| lia]| lia]. }
    eapply evt_cut.
    { eapply (raligned_move_walk x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp y5 y6 y7 (Z_to_bv 64 63) q1 a0
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6 F fc m P B E len i stride adj).
      - exact HP.
      - exact MI.
      - rewrite SEQ. eapply wr_at_sub; [exact WRr| unfold cz; clear - B0 SI0; lia| unfold E, eo, cz in *; clear - SPAN; lia].
      - unfold E, eo, ceil_window in *. clear - SPAN RBC RB0 RUP CEIL_RANGE__. lia.
      - unfold B. clear - B0 RB0. lia.
      - clear - Hi. lia.
      - clear - S16 ST20. lia.
      - rewrite SEQ. unfold P, po, cz. clear - OFF ADJ3. lia.
      - clear - ADJ3. lia.
      - exact LEN0.
      - unfold P, E, eo, po. clear - FIT' ADJE. fold d in ADJE. lia.
      - unfold P, E, eo, po. clear - ST20 OFF LEN0 ADJ3. lia.
      - unfold P, B, po. clear - Q1 FIT' SIC SCNT ADJE LEN0. fold d in ADJE. lia.
      - rewrite SEQ. unfold cz. clear - B0 SI0 RB0. lia. }
    intros ms2 (z5 & z6 & z7 & z8 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & m2 & -> & Em2 & MI2).
    rewrite SEQ in Em2.
    set (Cfp := fun x => r_base r + cz - 3 <= x < E /\ ~ (P + adj <= x < P + adj + len)).
    assert (PE2 : rpres_except Cfp m m2).
    { rewrite Em2. apply rpres_move; [apply rpres_except_refl| unfold cz; clear - B0 SI0 RB0; lia| unfold P, po, cz; clear - OFF ADJ3; lia| exact LEN0
                                     | unfold P, E, eo, po; clear - FIT' ADJE; fold d in ADJE; lia
                                     | unfold E, eo, ceil_window in *; clear - SPAN RBC RB0 RUP CEIL_RANGE__; lia|].
      intros x Hx NX. split; [exact Hx| exact NX]. }
    assert (HIGH : forall x, alloc_ceiling <= x -> ~ Cfp x) by (intros x Hx [X _]; unfold E, eo in *; clear - X Hx SPAN RBC; lia).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) (ra_frame j8 ra s0 s1)).
    { eapply rpres_except_rw_cells; [exact PE2| exact FR|]. intros x Hx. apply HIGH. clear - Hx LO SLO. lia. }
    assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -32)).
    { eapply rpres_except_stk; [exact PE2| exact ST|]. intros x Hx. apply HIGH. clear - Hx LO. lia. }
    eapply evt_cut.
    { eapply (raligned_epilogue x1 ra sp gp tp z5 z6 z7 s0 s1 z8 q1 (Z_to_bv 64 (P + adj)) z11 z12 z13 z14 z15 z16 z17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z28 t4 t5 t6 F fc m2 lo j8);
        [exact FR2| exact ST2| exact SLO| exact MI2]. }
    intros ms3 (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & -> & ST3).
    apply evt_done. right. split; [exact PM1|]. unfold raligned_ret_rep.
    exists u5, u6, u7, u11, u12, u13, u14, u15, u16, u17, u28, u29, u30, u31, m2.
    split; [reflexivity|].
    pose proof (rmove_mrep st m g bg r i MRm (ci_ticks _ _ C) (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) Hr Kr B0 ltac:(clear - Hi; lia)
                  ltac:(fold mr; fold stride; clear - SPAN; lia) ltac:(fold mr; fold stride; exact S16)
                  ltac:(fold mr; fold stride; exact NOGRP) (off + d) len ltac:(clear - OFF DR; lia) LEN0 ltac:(fold mr; fold stride; exact FIT')
                  ltac:(fold mr; fold stride; clear - ST20 LEN0; lia) ltac:(fold mr; fold stride; exact QR') ltac:(clear - OFF255 DR; lia)) as [MR2 TK2].
    fold mr in MR2, TK2. fold stride in MR2, TK2. rewrite <- Ec in MR2, TK2. fold cz in MR2.
    replace (snd bg + 16 + stride * i + stride - 4) with eo in MR2 by reflexivity. fold E in MR2.
    replace (r_base r + (cz + 16 * (off + d))) with (P + adj) in MR2 by (unfold P, po, cz; clear - ADJE; fold d in ADJE; lia).
    replace ((P + adj - B - 16) / 16) with ((cz + 16 * (off + d) - snd bg - 16) / 16) in Em2 by (f_equal; unfold P, B, po, cz; clear - ADJE; fold d in ADJE; lia).
    replace ((P + adj - (r_base r + cz)) / 16) with (off + d) in Em2.
    2:{ replace (P + adj - (r_base r + cz)) with ((off + d) * 16) by (unfold P, po, cz; clear - ADJE; fold d in ADJE; lia). rewrite Z.div_mul by (clear; lia). reflexivity. }
    rewrite <- Em2 in MR2.
    split; [exact MR2|]. split; [exact TK2|]. split; [exact MI2|]. split; [exact ST3| exact PE2].
Qed.
End REP.
End WithCeiling0.
