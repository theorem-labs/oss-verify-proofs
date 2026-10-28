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
  RF_realloc_head RF_realloc_arms RF_realloc_frame RF_realloc_hspec RMalloc_reframe.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma rpres_setsize : forall (Cfp : Z -> Prop) m0 m P E n k,
  rpres_except Cfp m0 m -> 16 <= P -> 0 <= n -> P + n <= E -> E + 5 <= 2^64 ->
  (forall x, P - 3 <= x < E -> ~ (P <= x < P + n) -> Cfp x) ->
  rpres_except Cfp m0 (rr_setsize_mem m P E n k).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros Cfp m0 m P E n k HP P16 N0 PE EHI HC.
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  unfold rr_setsize_mem. cbv zeta. set (rs := E - P - n).
  assert (H1 : rpres_except Cfp m0 (if rs =? 0 then m else write_to_mem m (wa (E - rs)) [b8 0])).
  { destruct (Z.eqb_spec rs 0) as [E0|NE]; [exact HP|].
    apply rpres_write; [exact HP| unfold rs; lia| cbn; unfold rs; lia| cbn; intros x Hx; apply HC; unfold rs in *; lia]. }
  apply rpres_write; [| lia | cbn; lia | cbn; intros x Hx; apply HC; lia].
  destruct (Z.leb_spec 5 rs) as [R5|R5]; [| exact H1].
  apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros x Hx; apply HC; unfold rs in *; lia].
  apply rpres_write; [exact H1 | lia | cbn; lia | cbn; intros x Hx; apply HC; unfold rs in *; lia].
Qed.

Section REP.
Variables (st : mstate) (LB : list block).
Variables (c : cptr) (off n0 : Z) (g bg : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis C : CINV st LB.
Hypothesis BF : blk_facts st c off n0 g bg i ai a ar ka.
Hypothesis INI : c_init_done (ctx st) <> 0.

Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let po := snd bg + 16 + stride * i + 16 * off.
Let eo := snd bg + 16 + stride * i + stride - 4.
Let res := eo - po - n0.
Let q := (po - snd bg - 16) / 16.

Lemma rrb_hosts : MallocFacts_B.hosts st bg g.
Proof. exists ai. exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). Qed.

Lemma rrb_geo : exists r, (s_regions st) !! (fst bg) = Some r /\ r_kind r = RKGroup
  /\ 0 <= snd bg /\ 16 <= stride /\ 0 <= stride * i /\ 0 <= i <= 31 /\ 0 <= off <= 291 /\ 0 <= n0
  /\ snd bg + 16 + stride * i + stride <= round_up_pg (r_len r)
  /\ 16 * off + n0 + 4 <= stride /\ 16 * off + 16 <= stride /\ 0 <= res
  /\ c = (fst bg, snd bg + 16 + stride * i)
  /\ po mod 16 = 0 /\ 16 * q = stride * i + 16 * off /\ 0 <= q < 2^16.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  pose proof (ci_gmetas _ _ C bg g rrb_hosts) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  exists r. split; [exact Hr|]. split; [exact Kr|].
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 SM]. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as LI. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as OFF. unfold OFF_MAX in OFF.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as N0. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT.
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec. pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as Hmem.
  change (MR st g) with mr in *. fold stride in S16, SM, FIT. unfold UNIT, IB in *.
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold sstart_of in SPAN. fold mr in SPAN. rewrite Hmem in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN. unfold UNIT in SPAN.
  assert (ESS : sstart mr i = snd bg + 16 + stride * i).
  { unfold sstart, gbase. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT. reflexivity. }
  rewrite ESS in Ec.
  pose proof (q16 st c off n0 g bg i ai a ar ka BF) as [Q1 Q2]. cbn [aadd snd] in Q1, Q2.
  rewrite Ec in Q1, Q2. cbn [snd] in Q1, Q2. change (MR st g) with mr in Q1. fold stride in Q1. unfold UNIT in Q1, Q2.
  replace ((snd bg + 16 + stride * i + 16 * off - snd bg - 16) / 16) with q in Q1, Q2 by (unfold q, po; reflexivity).
  split; [exact B0|]. split; [exact S16|]. split; [exact SI0|]. split; [lia|]. split; [exact OFF|]. split; [exact N0|].
  assert (O16 : 16 * off + 16 <= stride) by (clear - FIT N0 SM OFF S16; Z.div_mod_to_equations; lia).
  split; [lia|]. split; [lia|]. split; [exact O16|]. split; [unfold res, eo, po; lia|]. split; [exact Ec|].
  split; [| split; [exact Q1| exact Q2]].
  pose proof (p_mod16 st c off n0 g bg i ai a ar ka BF) as PM. cbn [aadd snd] in PM. rewrite Ec in PM. cbn [snd] in PM. unfold UNIT in PM. exact PM.
Qed.

Lemma rrealloc_head_bf : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r,
  rmrep st m -> mem_inv usegs m -> (s_regions st) !! (fst bg) = Some r ->
  bv_unsigned a0 = r_base r + po ->
  evt usegs (rrh_post ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 a1 F fc m (conc st g) (conc st bg) (m_sizeclass mr) (meta_word mr)
               (r_base r + eo) (r_base r + po) res)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b2768) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until r. intros MRm MI Hr HP.
  destruct rrb_geo as (r' & Hr' & Kr & B0 & S16 & SI0 & Hi & OFF & N0 & SPAN & FIT & O16 & RES0 & Ec & PM & Q1 & Q2).
  rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof (ci_gmetas _ _ C bg g rrb_hosts) as GO.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  rewrite (gbase_bm st c off n0 g bg i ai a ar ka BF) in SH. rewrite Ec in SH. cbn [fst snd] in SH.
  change (MR st g) with mr in SH. fold stride in SH. unfold UNIT, IB in SH.
  replace (snd bg + 16 + stride * i + 16 * off) with po in SH by reflexivity.
  replace (snd bg + 16 + stride * i + stride - 4) with eo in SH by reflexivity.
  replace ((po - snd bg - 16) / 16) with q in SH by reflexivity. fold res in SH.
  destruct SH as (K4 & K3 & K2 & K1 & _ & K5 & Kr0 & _). unfold known in K4, K3, K2, K1, K5, Kr0. cbn [fst snd] in K4, K3, K2, K1, K5, Kr0.
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. unfold known in H0. cbn [fst snd] in H0.
  rewrite sstart_succ in H0. change (MR st g) with mr in H0. fold stride in H0.
  assert (ESS : sstart mr i = snd bg + 16 + stride * i).
  { unfold sstart, gbase. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn [default from_option id snd]. unfold UNIT. reflexivity. }
  rewrite ESS in H0. unfold IB in H0. replace (snd bg + 16 + stride * i + stride - 4) with eo in H0 by reflexivity.
  pose proof (u16_bytes q Q2) as U16.
  assert (EIDX : Z.land (i + 32 * Z.min res 5) 31 = i) by (apply land31_idx; lia).
  assert (EBASE : aadd (fst bg, po) (- (UNIT * (byte_of q 0 + 256 * byte_of q 1)) - UNIT) = bg).
  { rewrite U16. unfold aadd, UNIT. cbn [fst snd]. destruct bg as [br bo]. cbn [fst snd] in *. f_equal. unfold po. cbn [snd]. lia. }
  destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Em).
  pose proof (blk_meta_guards st c off n0 g bg i ai a ar ka BF) as GU. cbv zeta in GU.
  rewrite Ec in GU. cbn [snd] in GU. change (MR st g) with mr in GU. fold stride in GU. unfold UNIT in GU.
  replace ((snd bg + 16 + stride * i + 16 * off - snd bg - 16) / 16) with q in GU by reflexivity.
  destruct GU as (_ & _ & G16 & G63 & G17).
  eapply evt_mono.
  { eapply (rrealloc_head_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              st (fst bg, po) r g (mkGhdr (Some g) ai) ar (i + 32 * Z.min res 5) (byte_of q 0) (byte_of q 1) res);
      cbn [fst snd]; rewrite ?EBASE, ?EIDX, ?U16; fold mr; fold stride; unfold UNIT, IB;
      replace (snd bg + 16 + stride * i + stride - 4) with eo by reflexivity.
    - exact MRm.
    - exact MI.
    - exact Hr.
    - exact Kr.
    - exact HP.
    - exact PM.
    - unfold po; clear - B0 SI0 OFF; lia.
    - unfold po; clear - Q1 B0; lia.
    - unfold po; clear - SPAN O16; lia.
    - exact K4.
    - exact K3.
    - exact K2.
    - exact K1.
    - exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF).
    - reflexivity.
    - exact (go_slot _ _ _ GO).
    - destruct (go_slot _ _ _ GO) as (a' & ara & k' & Ha' & Hk' & ->).
      pose proof MRm as ((_ & _ & _ & WA & _) & _). destruct (WA a' ara Ha') as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
    - exact (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF).
    - rewrite Em, (area_of_mslot a ka Hal Hka). exact Ha.
    - exact Hck.
    - exact INI.
    - exact (go_avail _ _ _ GO).
    - exact (go_freed _ _ _ GO).
    - exact (proj2 (proj2 (proj2 (proj2 (ci_cx _ _ C))))).
    - pose proof (go_li _ _ _ GO) as X. fold mr in X. lia.
    - rewrite (go_freeable _ _ _ GO). lia.
    - destruct (go_sc _ _ _ GO) as [X|(X & _)]; fold mr in X; lia.
    - pose proof (go_maplen _ _ _ GO) as X. fold mr in X. lia.
    - pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as X. change (MR st g) with mr in X. lia.
    - exact (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF).
    - exact (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF).
    - exact G16.
    - exact G63.
    - exact G17.
    - intros X. destruct (go_sc _ _ _ GO) as [Y|(Y1 & Y2 & Y3)]; [fold mr in Y; lia| fold mr in Y1, Y2, Y3; lia].
    - exact S16.
    - unfold eo, po. clear - O16. lia.
    - unfold eo. clear - SPAN. lia.
    - unfold res in *. clear - RES0 N0. lia.
    - destruct (Z.le_gt_cases 5 res) as [R5|R5]; [destruct (K5 R5) as (_ & _ & _ & _ & _ & X); exact X| lia].
    - reflexivity.
    - intros R5. destruct (K5 R5) as (F0 & F1 & F2 & F3 & F5 & _). unfold byte_of in F0, F1, F2, F3.
      change (8 * 0) with 0 in F0. change (8 * 1) with 8 in F1. change (8 * 2) with 16 in F2. change (8 * 3) with 24 in F3.
      replace (eo - 4 + 1) with (eo - 3) by lia. replace (eo - 4 + 2) with (eo - 2) by lia. replace (eo - 4 + 3) with (eo - 1) by lia.
      repeat split; assumption.
    - destruct (Z.eq_dec res 0) as [E0|NE]; [rewrite E0, Z.sub_0_r; exact H0| apply Kr0; lia].
    - exact H0. }
  intros ms' PO. cbn [fst snd] in PO. rewrite ?EBASE, ?EIDX, ?U16 in PO. fold mr in PO. fold stride in PO. unfold UNIT, IB in PO.
  replace (snd bg + 16 + stride * i + stride - 4) with eo in PO by reflexivity. exact PO.
Qed.

(* [comment removed for export] *)
Definition rrealloc_grow_rep (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo n ER : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x2b2aa8) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 n) a0 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                  (wz ER) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b14ec) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6)
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Definition rrealloc_inplace_rep (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo n : Z) (r : region) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ rmrep (rf_setsize_st st c g bg i off n) m' /\ ticks_ok (rf_setsize_st st c g bg i off n)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rpres_except (fun x => bv_unsigned sp - 64 <= x < bv_unsigned sp
                              \/ (r_base r + po - 3 <= x < r_base r + eo /\ ~ (r_base r + po <= x < r_base r + po + n))) m m'
    /\ 16 * off + n + 4 <= stride /\ stride < 2^20.

Theorem rrealloc_pre_rep : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo r n,
  rmrep st m -> mem_inv usegs m -> (s_regions st) !! (fst bg) = Some r ->
  bv_unsigned a0 = r_base r + po -> a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  (m_sizeclass mr < 48 -> stride < 2^20) ->
  (forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst bg ->
     snd b' + 9 <= snd bg + 16 + stride * i - 4 \/ snd bg + 16 + stride * i + stride - 4 <= snd b') ->
  evt usegs (fun ms' => rrealloc_grow_rep ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc lo n (r_base r + po + n0) m ms'
                        \/ rrealloc_inplace_rep ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc lo n r m ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b270c) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until n. intros MRm MI Hr HP HA1 N ST LO SLO S20 NOGRP.
  destruct rrb_geo as (r' & Hr' & Kr & B0 & S16 & SI0 & Hi & OFF & N0 & SPAN & FIT & O16 & RES0 & Ec & PM & Q1 & Q2).
  rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof (ci_gmetas _ _ C bg g rrb_hosts) as GO.
  pose proof MRm as (WF & _ & _ & _ & _ & SHm). pose proof WF as (_ & WR & _).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (POR : 16 <= po /\ po + 16 <= round_up_pg (r_len r)) by (unfold po; clear - B0 SI0 OFF SPAN O16; lia).
  assert (EOR : po + n0 <= eo /\ eo + 4 <= round_up_pg (r_len r)) by (unfold po, eo; clear - FIT SPAN; lia).
  unfold MMAP_THRESHOLD in N.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rrealloc_prologue ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo).
    - rewrite HP. lia.
    - rewrite HA1, unsigned_lit by lia. lia.
    - exact ST.
    - unfold ceil_window in *. lia.
    - exact SLO.
    - exact MI. }
  intros ms1 (a2' & m1 & -> & FR & ST1 & MU & WM & MI1).
  assert (MR1 : rmrep st m1).
  { eapply rmrep_transport_high; [exact MRm| exact MU| exact WM|]. intros l h [E|[]]. inversion E; subst. lia. }
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rrealloc_head_bf ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 r);
      [exact MR1| exact MI1| exact Hr| exact HP]. }
  intros ms2 (t1' & t2' & t3' & t4' & ->).
  (* [comment removed for export] *)
  assert (SCR : 0 <= m_sizeclass mr < 64) by (destruct (go_sc _ _ _ GO) as [X|(X & _)]; fold mr in X; lia).
  eapply evt_cut.
  { eapply (rrealloc_arms_walk ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t1' t2' s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 F fc m1
              n (conc st g) (conc st bg) (m_sizeclass mr) (meta_word mr) (r_base r + eo) (r_base r + po) (r_base r + eo - res));
      [exact HA1| unfold MMAP_THRESHOLD; exact N| exact MI1| exact SCR|].
    unfold ceil_window in *. pose proof (round_up_pg_ge (r_len r)). clear - POR EOR RBC RB0 N0 CEIL_RANGE__. lia. }
  intros ms3 [[GROW _]|[INP (LE & SCLE)]].
  - (* [comment removed for export] *)
    apply evt_done. left. destruct GROW as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & ->).
    unfold rrealloc_grow_rep. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, t5, t6, m1.
    replace (r_base r + po + n0) with (r_base r + eo - res) by (unfold res; lia).
    split; [reflexivity|]. split; [exact FR|]. split; [exact ST1|]. split; [exact MU|]. split; [exact WM| exact MI1].
  - (* [comment removed for export] *)
    destruct INP as (x6 & x7 & x12 & x13 & x14 & x15 & x17 & x28 & x29 & ->).
    assert (SC48 : m_sizeclass mr < 48).
    { pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD; lia)) as (SCN & _). destruct (go_sc _ _ _ GO) as [X|(X & _)]; fold mr in X; lia. }
    pose proof (S20 SC48) as ST20.
    assert (LE' : po + n <= eo) by lia.
    set (b3 := i + 32 * Z.min res 5).
    assert (B3R : 0 <= b3 < 256) by (unfold b3; lia).
    assert (EIDX : Z.land b3 31 = i) by (apply land31_idx; lia).
    pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 _ r Hr Kr) as [WRr HBr].
    pose proof (round_up_pg_ge (r_len r)) as RUP.
    (* [comment removed for export] *)
    pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
    rewrite Ec in SH. cbn [fst snd] in SH. change (MR st g) with mr in SH. fold stride in SH. unfold UNIT, IB in SH.
    replace (snd bg + 16 + stride * i + 16 * off) with po in SH by reflexivity.
    replace (snd bg + 16 + stride * i + stride - 4) with eo in SH by reflexivity. fold res in SH. fold b3 in SH.
    destruct SH as (_ & K3 & _). unfold known in K3. cbn [fst snd] in K3.
    destruct (HBr (po - 3) b3 ltac:(lia) K3) as [BK3 _].
    eapply evt_cut.
    { eapply (rrealloc_inplace_walk ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x6 x7 s0 (wz (conc st g)) a0 x12 x13 x14 x15 x17
                (wz (r_base r + eo - res)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6 F fc m1 (r_base r + po) (r_base r + eo) n b3).
      - exact HP.
      - exact MI1.
      - eapply wr_at_sub; [exact WRr| lia| lia].
      - replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia. exact BK3.
      - exact B3R.
      - unfold ceil_window in *. lia.
      - lia.
      - lia.
      - lia.
      - unfold eo, po in *. lia. }
    intros ms4 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & m2 & -> & Em2 & MI2).
    rewrite EIDX in Em2.
    (* [comment removed for export] *)
    set (Cfp := fun x => r_base r + po - 3 <= x < r_base r + eo /\ ~ (r_base r + po <= x < r_base r + po + n)).
    assert (PE2 : rpres_except Cfp m1 m2).
    { rewrite Em2. apply rpres_setsize; [apply rpres_except_refl| lia| lia| lia| unfold ceil_window in *; lia|].
      intros x Hx NX. split; assumption. }
    assert (HIGH : forall x, alloc_ceiling <= x -> ~ Cfp x) by (intros x Hx [X _]; lia).
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6)).
    { eapply rpres_except_rw_cells; [exact PE2| exact FR|]. intros x Hx. apply HIGH. lia. }
    assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -64)).
    { eapply rpres_except_stk; [exact PE2| exact ST1|]. intros x Hx. apply HIGH. lia. }
    eapply evt_cut.
    { eapply (rrealloc_epilogue ra ra sp gp tp y5 y6 y7 s0 s1 s2 s3 s4 s5 s6 s0 (wz (conc st g)) (wz (r_base r + eo - res)) s3 s4 s5 s6
                a0 y11 y12 y13 y14 y15 y16 y17 s7 s8 s9 s10 s11 y28 y29 t5 t6 F fc m2 lo); [exact FR2| exact ST2| exact SLO| exact MI2]. }
    intros ms5 (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & -> & ST3).
    apply evt_done. right. unfold rrealloc_inplace_rep.
    exists z5, z6, z7, z11, z12, z13, z14, z15, z16, z17, z28, z29, z30, z31, m2.
    split; [reflexivity|].
    (* [comment removed for export] *)
    pose proof (rsetsize_mrep st m1 g bg r i MR1 (ci_ticks _ _ C) (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) Hr Kr B0 ltac:(lia)
                  ltac:(fold mr; fold stride; clear - SPAN; lia) ltac:(fold mr; fold stride; exact S16)
                  ltac:(fold mr; fold stride; exact NOGRP) off n ltac:(lia) ltac:(lia) ltac:(fold mr; fold stride; unfold eo, po in LE'; lia)
                  ltac:(fold mr; fold stride; lia)) as [MR2 TK2].
    fold mr in MR2, TK2. fold stride in MR2, TK2. rewrite <- Ec in MR2, TK2.
    replace (snd bg + 16 + stride * i + 16 * off) with po in MR2 by reflexivity.
    replace (snd bg + 16 + stride * i + stride - 4) with eo in MR2 by reflexivity.
    rewrite <- Em2 in MR2.
    split; [exact MR2|]. split; [exact TK2|]. split; [exact MI2|]. split; [exact ST3|].
    split; [| split; [unfold eo, po in LE'; lia| exact ST20]].
    eapply rpres_except_trans.
    + eapply (rpres_except_of_munch _ [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1); [exact MU| exact WM|].
      intros x Hx NC. cbn [outside]. split; [| exact I]. intros X. apply NC. left. exact X.
    + eapply rpres_except_mono; [exact PE2|]. intros x Hx. right. exact Hx.
Qed.
End REP.
End WithCeiling0.
