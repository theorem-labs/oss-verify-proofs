(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA EdgesA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition RA_CM_MALLOC : Z := 0x1f2694.     (* [comment removed for export] *)
Definition CRYPTO_MALLOC_STACK : Z := 48 + RT_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Local Notation MAL := (rc_malloc RT (@ar_RC AR)).
(* [comment removed for export] *)
Lemma GOTC : forall Σ m, ART RT Σ m ->
  ro_cells bsegs m CR_GOT_MALLOC [C8 (wz CRYPTO_MALLOC)] /\ ro_cells bsegs m CR_GOT_FREE [C8 (wz CRYPTO_FREE)].
Proof.
  intros Σ m HA. destruct (af_client_consts RT AF Σ m HA) as (_ & _ & _ & _ & R).
  split; apply (relro_ro_cells m _ _ R); try (vm_compute; reflexivity); try (cbn; repeat split);
    unfold RELRO_LO, RELRO_HI, CR_GOT_MALLOC, CR_GOT_FREE; cbn; lia.
Qed.
Local Notation E_cm_leaf := (E_CRYPTO_malloc_1f6f74 : uk_leaf CRYPTO_MALLOC RA_CM_MALLOC).

(* [comment removed for export] *)
Definition mal_R (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (n lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms => exists p m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
    /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
    /\ wr_at bsegs m' p n /\ acc bsegs m' p n
    /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Lemma malloc_post_R : forall Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m c,
  malloc_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m c ->
  exists Σ', ASTA RT Σ' PMc (mal_R Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m Σ') c.
Proof.
  intros until c. intros (Σ' & p & HA & P1 & P2 & P3 & P4 & P5 & P6 & P7). exists Σ'.
  eapply ASTA_conseq; [exact HA|]. intros ms (m' & H1 & H2 & H3 & H4 & H5). exists p, m'. auto 15.
Qed.

(* [comment removed for export] *)
Definition calloc_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (n lo : Z) (m : mem) (init : Z -> mem -> Prop)
    (p : bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' A,
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ - MC <= rt_credit RT Σ'
    /\ ablock_range A n /\ AHEAP Σ' ((p, A, n) :: OW) LB m' /\ acc bsegs m' A n /\ init A m'.

Lemma CRYPTO_malloc_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (n lo : Z) (ras : list Z)
    (k : option bptr -> btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_MALLOC_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  crypto_statics m -> a0 = wz n -> 0 < n < 2^32 ->
  Z.of_nat (length (OW ++ LB)) < LIVE_MAX -> MC <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_MALLOC (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB n lo m
                  (fun A m' => exists junk, rw_cells bsegs m' A [CB (Z.to_nat n) junk]) p Σ' ms' ->
     implA (k (Some p)) Σ' Q ms') ->
  implA (TMalloc n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_MALLOC) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS -> Hn LIVE CRED UW CTX K.
  unfold CRYPTO_MALLOC_STACK, RT_STACK, CRYPTO_MALLOC, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct CS as (CS3 & CS4 & CS5 & CS6).
  destruct (GOTC Σ m (AH_art _ _ _ _ HEAP)) as (G1 & _).
  unfold CR_GOT_MALLOC, CR_MALLOC_IMPL, CR_NO_CUSTOMIZE, CRYPTO_MALLOC, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply implA_from_evt.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 13 step.
  step. step. if_true.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
  step. step. step. if_true.
  step. step.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (HEAP0 : AHEAP Σ OW LB m0).
  { eapply (seg_heap Σ OW LB m m0 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (UW0 : uw_chain USTACK_TOP m0 (bv_unsigned sp + -48) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m0 _ (bv_unsigned sp) 48 [CB 8 (take 8 junk); C8 s3; C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  apply evt_done.
  eapply implA_malloc with (avoid := map blk_id (OW ++ LB)).
  - intros Hn'.
    eapply cps_conseq; [ eapply (MAL Σ PMc) with (n := n) (lo := lo); try reflexivity | intros c Hc; exact Hc
                       | intros c Hc; exact (malloc_post_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) ].
    + exact ar_PMc_fdfs.
    + exact ar_PMc_ms.
    + unfold BSZ in Hn'. lia.
    + rewrite (AH_live_len _ _ _ _ HEAP0). exact LIVE.
    + pose proof (mcost_le_MC n Hn'). lia.
    + exact (AH_art _ _ _ _ HEAP0).
    + exact MI.
    + unfold call_ok. rewrite ESP. destruct HEAP0 as (_ & HS & _). rewrite HS. fold ACEIL.
      split; [exact ST|]. unfold RT_STACK, USTACK_TOP. split; [unfold BnHeapA.ACEIL in *; lia|]. split; [lia|]. split; [lia|].
      clear - SP16. Z.div_mod_to_equations. lia.
    + eapply unwind_ch_intro with (ras := bv_unsigned ra :: ras).
      * rewrite unsigned_lit by lia. exact (uk_ctx_leaf _ _ _ E_cm_leaf CTX).
      * rewrite ESP. exact UW0.
  - intros p Σ' ms' Hn' Hp (A & m1 & RS & (ART1 & MI1 & WM1 & ST1) & PRES & WR1 & ACC1 & LV1 & FR1 & SP1 & CR1 & A0 & A16 & ATOP).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    rewrite ESP in ST1, PRES.
    rewrite (ret_pc_even 2041492) by lia.
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold USTACK_TOP in ATOP; lia).
    pose proof HEAP0 as (_ & HS0 & HF0 & HL0 & _).
    assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp + -48)) m0 m1).
    { eapply (AH_agree _ _ _ _ _ _ _ HEAP0). rewrite <- HF0. exact PRES. }
    apply (rw_cells_agree _ _ _ _ _ AG1) in FR; [| intros a Ha; left; cbn in Ha; unfold USTACK_TOP; lia].
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl bsegs m1) as WMr.
    apply implA_from_evt.
    step. if_cases KA; zify_cond KA; [| exfalso; rewrite ?EA in KA; lia]. clear KA.
    do 6 step.
    release_frame FR ST1 (bv_unsigned sp).
    step.
    apply evt_done. apply (K p Σ' _ Hp).
    unfold calloc_postA, MallocRep.wz.
    do 16 eexists. exists m1, A. split; [reflexivity|].
    split; [exact MI1|]. split; [exact ST1|].
    split.
    { eapply agree_on_trans.
      - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a [Ha|[Ha|Ha]]; cbn [outside]; (split; [|exact I]).
        + lia.
        + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
          destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold BnHeapA.ACEIL in *; lia.
        + destruct Ha as (b & Hb & Hr). pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). lia.
      - eapply agree_on_mono; [exact AG1|]. intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha]. }
    split; [rewrite CR1; pose proof (mcost_le_MC n Hn'); lia|].
    assert (HEAP1 : AHEAP Σ' ((p, A, n) :: OW) LB m1).
    { eapply (AH_malloc Σ Σ' OW LB m0 m1 p A n HEAP0 ART1 LV1 FR1 SP1 A16); [lia | exact Hp]. }
    split; [exact (AH_range _ _ _ _ p A n HEAP1 (or_introl eq_refl))|].
    split; [exact HEAP1|]. split; [exact ACC1|].
    exact (wr_at_rw_CB m1 A n WR1 ltac:(lia)).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation FRE := (rc_free RT (@ar_RC AR)).
Local Notation E_cf_tail := (E_CRYPTO_free_1f7454 : uk_leaf_tail CRYPTO_FREE).

Definition CRYPTO_FREE_STACK : Z := 16 + RT_STACK.

Definition fre_R (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (A lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
    /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m'
    /\ rt_live RT Σ' = live_remove A (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ.

Lemma free_post_R : forall Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A lo m c,
  free_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A lo m c ->
  exists Σ', ASTA RT Σ' PMc (fre_R Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 A lo m Σ') c.
Proof.
  intros until c. intros (Σ' & v & HA & P1 & P2 & P3 & P4). exists Σ'.
  eapply ASTA_conseq; [exact HA|]. intros ms (m' & H1 & H2 & H3). exists v, m'. auto 10.
Qed.

Definition cfree_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (p : bptr) (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (lb_remove p (OW ++ LB)) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ' = rt_credit RT Σ
    /\ AHEAP Σ' (lb_remove p OW) LB m'.

Lemma CRYPTO_free_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (p : bptr) (A n lo : Z) (ras : list Z)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m -> In (p, A, n) OW ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  crypto_statics m -> a0 = wz A ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_FREE (bv_unsigned ra :: ras) ->
  (forall Σ' ms', cfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p lo m Σ' ms' -> implA k Σ' Q ms') ->
  implA (TFree p k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_FREE) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HEAP IN ST CEIL LO SPT SP16 MI -> CS -> UW CTX K.
  unfold CRYPTO_FREE_STACK, RT_STACK, CRYPTO_FREE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct CS as (CS3 & CS4 & CS5 & CS6).
  destruct (GOTC Σ m (AH_art _ _ _ _ HEAP)) as (_ & G2).
  unfold CR_GOT_FREE, CR_FREE_IMPL, CRYPTO_FREE, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply implA_from_evt.
  carve_frame 16%nat ST. do 8 step. step. if_true.
  do 2 step.
  release_frame FR ST (bv_unsigned sp). step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  assert (INL : In (A, n) (rt_live RT Σ)) by exact (AH_live _ _ _ _ (p, A, n) HEAP1 (in_or_app _ _ _ (or_introl IN))).
  apply evt_done.
  eapply implA_free.
  - eapply cps_conseq; [ eapply (FRE Σ PMc) with (p := A) (n := n) (lo := lo); try reflexivity | intros c Hc; exact Hc
                       | intros c Hc; exact (free_post_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) ].
    + exact ar_PMc_fdfs.
    + exact ar_PMc_ms.
    + exact INL.
    + exact (AH_art _ _ _ _ HEAP1).
    + exact MI.
    + unfold call_ok. destruct HEAP1 as (_ & HS & _). rewrite HS. fold ACEIL.
      split; [exact ST|]. unfold RT_STACK, USTACK_TOP. split; [unfold BnHeapA.ACEIL in *; lia|]. split; [lia|]. split; [lia | exact SP16].
    + eapply unwind_ch_intro with (ras := ras); [exact (uk_ctx_leaf_tail _ _ E_cf_tail CTX) | exact UW1].
  - intros Σ' ms' (v & m2 & RS & (ART2 & MI2 & ST2) & PRES & LV2 & FR2 & SP2 & CR2).
    apply K. unfold cfree_postA, MallocRep.wz.
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    assert (HEAP2 : AHEAP Σ' (lb_remove p OW) LB m2) by exact (AH_free Σ Σ' OW LB m1 m2 p A n HEAP1 IN ART2 LV2 FR2 SP2).
    do 17 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split.
    { eapply agree_on_trans.
      - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a [Ha|[Ha|Ha]]; cbn [outside]; (split; [|exact I]).
        + lia.
        + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
          destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold BnHeapA.ACEIL in *; lia.
        + destruct Ha as (b & Hb & Hr). apply lb_remove_incl in Hb. pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). lia.
      - pose proof HEAP2 as (_ & _ & _ & HL2 & _). pose proof HEAP1 as (_ & _ & HF1 & _ & ND1 & _).
        rewrite (lb_remove_app_l p OW LB ND1) by (apply in_map_iff; exists (p, A, n); split; [reflexivity | exact IN]).
        eapply (AH_agree _ _ _ _ _ _ _ HEAP2). rewrite <- HF1. exact PRES. }
    split; [exact CR2 | exact HEAP2].
Qed.


(* [comment removed for export] *)
Definition cfree_null_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m'.

Lemma CRYPTO_free_null_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (ras : list Z),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A -> crypto_statics m -> a0 = wz 0 ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_FREE (bv_unsigned ra :: ras) ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz CRYPTO_FREE) fc None m (seg_rom bsegs))))
            (ASTA RT Σ PMc (cfree_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m)).
Proof.
  intros until ras. intros HEAP ST CEIL LO SPT SP16 MI -> CS -> UW CTX.
  unfold CRYPTO_FREE_STACK, RT_STACK, CRYPTO_FREE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct CS as (CS3 & CS4 & CS5 & CS6).
  destruct (GOTC Σ m (AH_art _ _ _ _ HEAP)) as (_ & G2).
  unfold CR_GOT_FREE, CR_FREE_IMPL, CRYPTO_FREE, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply cps_from_evt'.
  carve_frame 16%nat ST. do 8 step. step. if_true.
  do 2 step.
  release_frame FR ST (bv_unsigned sp). step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  apply evt_done.
  eapply cps_conseq; [ eapply (rc_free_null RT (@ar_RC AR) Σ PMc) with (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - exact (AH_art _ _ _ _ HEAP1).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP1 | exact ST | exact CEIL | unfold RT_STACK; lia | unfold USTACK_TOP; lia | exact SP16].
  - eapply unwind_ch_intro with (ras := ras); [exact (uk_ctx_leaf_tail _ _ E_cf_tail CTX) | exact UW1].
  - intros c (v & Hc). eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & _).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold cfree_null_post, MallocRep.wz. do 17 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact (AH_same _ _ _ _ _ HEAP1 ART2)|].
    eapply agree_on_trans; [exact AG1|].
    pose proof (AH_frames _ _ _ _ HEAP1) as HF1.
    eapply agree_on_mono; [eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP1); rewrite <- HF1; exact PRES|].
    intros x Hx. split; [exact Hx | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation AMSET := (rc_asan_memset RT (@ar_RC AR)).
Definition CRYPTO_ZALLOC : Z := 0x1f26e8.
Definition RA_CZ_MALLOC : Z := 0x1f2708.
Definition CRYPTO_ZALLOC_STACK : Z := 32 + CRYPTO_MALLOC_STACK.
Local Notation E_cz_call := (E_CRYPTO_zalloc_1f6fe8 : uk_call CRYPTO_ZALLOC RA_CZ_MALLOC CRYPTO_MALLOC).

Lemma CRYPTO_zalloc_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (n lo : Z) (ras : list Z)
    (k : option bptr -> btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_ZALLOC_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  crypto_statics m -> a0 = wz n -> 0 < n < 2^32 ->
  Z.of_nat (length (OW ++ LB)) < LIVE_MAX -> MC <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_ZALLOC (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB n lo m
                  (fun A m' => rw_cells bsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]) p Σ' ms' ->
     implA (k (Some p)) Σ' Q ms') ->
  implA (TMalloc n k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_ZALLOC) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS -> Hn LIVE CRED UW CTX K.
  unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, CRYPTO_ZALLOC, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  destruct CS as (CS3 & CS4 & CS5 & CS6).
  unfold CR_MEMSET_FUNC, CR_MALLOC_IMPL, CR_FREE_IMPL, CR_NO_CUSTOMIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply implA_from_evt.
  carve_frame 32%nat ST.
  do 8 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { apply (uw_push_frame m1 _ (bv_unsigned sp) 32 [C8 s2; C8 s1] (bv_unsigned ra) (bv_unsigned s0) ras);
      [reflexivity | lia | clear - SP16; Z.div_mod_to_equations; lia | unfold USTACK_TOP; lia | apply bv_unsigned_in_range | |].
    - rewrite !Z_to_bv_bv_unsigned. exact FR.
    - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  apply evt_done.
  eapply (CRYPTO_malloc_walkA) with (n := n) (lo := lo) (ras := bv_unsigned ra :: ras) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - rewrite ESP. exact ST.
  - exact CEIL.
  - rewrite ESP. unfold CRYPTO_MALLOC_STACK, RT_STACK. lia.
  - rewrite ESP. unfold USTACK_TOP. lia.
  - rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
  - exact MI.
  - unfold crypto_statics, CR_MEMSET_FUNC, CR_MALLOC_IMPL, CR_FREE_IMPL, CR_NO_CUSTOMIZE. auto.
  - exact Hn.
  - exact LIVE.
  - exact CRED.
  - rewrite ESP. exact UW1.
  - rewrite unsigned_lit by lia. exact (uk_ctx_call _ _ _ _ E_cz_call CTX).
  - intros p Σ' ms' Hp PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & A & -> & MI2 & ST2 & AG2 & CR2 & BR2 & HEAP2 & ACC2 & (junkA & BLK)).
    rewrite ESP in ST2, AG2.
    rewrite (ret_pc_even 2041608) by lia.
    pose proof BR2 as (A0 & A16 & _ & ACE & AIMG).
    assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; unfold USTACK_TOP; lia].
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m2) as MU2. pose proof (wmono_refl bsegs m2) as WM2.
    apply implA_from_evt.
    step. step. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA in KA; lia|]. clear KA.
    do 4 step.
    apply evt_done.
    eapply implA_step_same.
    + eapply (AMSET Σ' PMc) with (d := A) (n := n) (c := Z_to_bv 8 0) (lo := lo); try reflexivity.
      * exact ar_PMc_fdfs.
      * exact ar_PMc_ms.
      * unfold BnHeapA.ACEIL in *. lia.
      * lia.
      * assert (INL : In (A, n) (rt_live RT Σ')) by exact (AH_live _ _ _ _ (p, A, n) HEAP2 (or_introl eq_refl)).
        split; [intros _; split; [exact ACC2 | left; exists A, n; split; [exact INL | lia]] |].
        split; [intros i Hi; right; right; left; exists A, n; split; [exact INL | lia] |].
        destruct BLK as [_ W]. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W.
      * exact (AH_art _ _ _ _ HEAP2).
      * exact MI2.
      * unfold call_ok. rewrite ESP. destruct HEAP2 as (_ & HS & _). rewrite HS. fold ACEIL.
        split; [exact ST2|]. unfold RT_STACK, USTACK_TOP. split; [unfold BnHeapA.ACEIL in *; lia|]. split; [lia|]. split; [lia|].
        clear - SP16. Z.div_mod_to_equations. lia.
    + intros ms3 (m3 & RS & (ART3 & MI3 & WM3 & ST3) & PRES3 & BZ).
      destruct RS as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
      rewrite ESP in ST3, PRES3.
      rewrite (ret_pc_even 2041632) by lia.
      pose proof HEAP2 as (_ & _ & HF2 & HL2 & _).
      assert (AG3 : agree_on (fun a => aclient_addr (((p, A, n) :: OW) ++ LB) (bv_unsigned sp + -32) a /\ ~ (A <= a < A + n)) m2 m3).
      { eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP2). rewrite <- HF2. exact PRES3. }
      apply (rw_cells_agree _ _ _ _ _ AG3) in FR;
        [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia]].
      pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m3) as MU3. pose proof (wmono_refl bsegs m3) as WMr.
      apply implA_from_evt.
      do 6 step.
      release_frame FR ST3 (bv_unsigned sp).
      step.
      apply evt_done. apply (K p Σ' _ Hp).
      unfold calloc_postA, MallocRep.wz.
      do 16 eexists. exists m3, A. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|].
      split.
      { eapply agree_on_trans; [eapply agree_on_trans|].
        - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a [Ha|[Ha|Ha]]; cbn [outside]; (split; [|exact I]).
          + lia.
          + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
            destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold BnHeapA.ACEIL in *; lia.
          + destruct Ha as (b & Hb & Hr). pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). lia.
        - eapply agree_on_mono; [exact AG2|]. intros a [Ha|[Ha|Ha]]; [left; lia | right; left; exact Ha | right; right; exact Ha].
        - eapply agree_on_mono; [exact AG3|]. intros a Ha. split.
          + destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; lia | right; left; exact Ha | right; right; exists b; split; [right; exact Hb | exact Hr]].
          + (* [comment removed for export] *)
            intros HAr. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
            * unfold BnHeapA.ACEIL in *. lia.
            * eapply (blk_not_static Σ' ((p, A, n) :: OW) LB m2 (p, A, n) a HEAP2 (or_introl eq_refl)); [cbn; lia | exact Ha].
            * assert (NE : blk_id b <> p).
              { intros E. apply Hp. rewrite <- E. apply in_map. exact Hb. }
              pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) HEAP2 (or_intror Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. lia. }
      split; [exact CR2|]. split; [exact BR2|].
      assert (HEAP3 : AHEAP Σ' ((p, A, n) :: OW) LB m3) by exact (AH_same _ _ _ _ _ HEAP2 ART3).
      split; [exact HEAP3|].
      split; [exact (proj2 (AH_acc _ _ _ _ (p, A, n) HEAP3 (or_introl eq_refl)))|].
      split; [split |].
      * cbn [cells_wf cell_wf]. split; [apply repeat_length | exact I].
      * cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact BZ.
      * cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        destruct BLK as [_ W]. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia.
        exact (wr_at_transport bsegs m2 m3 A n W WM3).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CRYPTO_CALLOC : Z := 0x1fce78.
Definition CRYPTO_MALLOC_ARRAY : Z := 0x1fcde4.
Definition CRYPTO_CALLOC_STACK : Z := 32 + CRYPTO_ZALLOC_STACK.
Definition CRYPTO_MALLOC_ARRAY_STACK : Z := 32 + CRYPTO_MALLOC_STACK.
Local Notation E_cc_tail := (E_CRYPTO_calloc_2010e4 : uk_tail CRYPTO_CALLOC CRYPTO_ZALLOC).
Local Notation E_cma_tail := (E_CRYPTO_malloc_array_201050 : uk_tail CRYPTO_MALLOC_ARRAY CRYPTO_MALLOC).

Lemma calloc_postA_weaken : forall ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB n lo m m1 init p Σ' ms',
  agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1 ->
  calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB n lo m1 init p Σ' ms' ->
  calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB n lo m init p Σ' ms'.
Proof.
  intros until ms'. intros AG (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m2 & A & E & MI2 & ST2 & AG2 & Rest).
  do 16 eexists. exists m2, A. split; [exact E|]. split; [exact MI2|]. split; [exact ST2|].
  split; [eapply agree_on_trans; [exact AG | exact AG2] | exact Rest].
Qed.

Lemma CRYPTO_calloc_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (num size lo : Z) (ras : list Z)
    (k : option bptr -> btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_CALLOC_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  crypto_statics m -> a0 = wz num -> a1 = wz size -> 0 < num -> 0 < size -> num * size < 2^32 ->
  Z.of_nat (length (OW ++ LB)) < LIVE_MAX -> MC <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_CALLOC (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB (num * size) lo m
                  (fun A m' => rw_cells bsegs m' A [CB (Z.to_nat (num * size)) (repeat (Z_to_bv 8 0) (Z.to_nat (num * size)))]) p Σ' ms' ->
     implA (k (Some p)) Σ' Q ms') ->
  implA (TMalloc (num * size) k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_CALLOC) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS -> -> Hnum Hsize Hn LIVE CRED UW CTX K.
  unfold CRYPTO_CALLOC_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, CRYPTO_CALLOC, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (Hsz : num < 2^32 /\ size < 2^32) by nia.
  apply implA_from_evt.
  carve_frame 32%nat ST. do 6 step. step. step. step.
  rewrite (unsigned_lit num), (unsigned_lit size) by lia.
  replace (Z.shiftr (num * size) 64) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_true.
  step. rewrite (unsigned_lit num), (unsigned_lit size) by lia.
  do 7 step. release_frame FR ST (bv_unsigned sp). step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  apply evt_done.
  eapply (CRYPTO_zalloc_walkA) with (n := num * size) (lo := lo) (ras := ras) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - exact ST.
  - exact CEIL.
  - unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK. lia.
  - unfold USTACK_TOP. lia.
  - exact SP16.
  - exact MI.
  - exact CS1.
  - nia.
  - exact LIVE.
  - exact CRED.
  - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor].
  - exact (uk_ctx_tail _ _ _ E_cc_tail CTX).
  - intros p Σ' ms' Hp PO. apply (K p Σ' ms' Hp). eapply calloc_postA_weaken; [exact AG1 | exact PO].
Qed.

Lemma CRYPTO_malloc_array_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (num size lo : Z) (ras : list Z)
    (k : option bptr -> btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_MALLOC_ARRAY_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  crypto_statics m -> a0 = wz num -> a1 = wz size -> 0 < num -> 0 < size -> num * size < 2^32 ->
  Z.of_nat (length (OW ++ LB)) < LIVE_MAX -> MC <= rt_credit RT Σ ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_MALLOC_ARRAY (bv_unsigned ra :: ras) ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     calloc_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB (num * size) lo m
                  (fun A m' => exists junk, rw_cells bsegs m' A [CB (Z.to_nat (num * size)) junk]) p Σ' ms' ->
     implA (k (Some p)) Σ' Q ms') ->
  implA (TMalloc (num * size) k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_MALLOC_ARRAY) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> CS -> -> Hnum Hsize Hn LIVE CRED UW CTX K.
  unfold CRYPTO_MALLOC_ARRAY_STACK, CRYPTO_MALLOC_STACK, RT_STACK, CRYPTO_MALLOC_ARRAY, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (Hsz : num < 2^32 /\ size < 2^32) by nia.
  apply implA_from_evt.
  carve_frame 32%nat ST. do 6 step. step. step. step.
  rewrite (unsigned_lit num), (unsigned_lit size) by lia.
  replace (Z.shiftr (num * size) 64) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_true.
  step. rewrite (unsigned_lit num), (unsigned_lit size) by lia.
  do 7 step. release_frame FR ST (bv_unsigned sp). step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (CS1 : crypto_statics m1).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | | exact CS].
    intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_A. cbn [rin_ivs fst snd]. unfold BnHeapA.ACEIL in *. lia. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  apply evt_done.
  eapply (CRYPTO_malloc_walkA) with (n := num * size) (lo := lo) (ras := ras) (OW := OW) (LB := LB); try reflexivity.
  - exact HEAP1.
  - exact ST.
  - exact CEIL.
  - unfold CRYPTO_MALLOC_STACK, RT_STACK. lia.
  - unfold USTACK_TOP. lia.
  - exact SP16.
  - exact MI.
  - exact CS1.
  - nia.
  - exact LIVE.
  - exact CRED.
  - eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor].
  - exact (uk_ctx_tail _ _ _ E_cma_tail CTX).
  - intros p Σ' ms' Hp PO. apply (K p Σ' ms' Hp). eapply calloc_postA_weaken; [exact AG1 | exact PO].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation MSET := (rc_memset RT (@ar_RC AR)).
Definition OPENSSL_CLEANSE : Z := 0x1f25ec.
Definition OPENSSL_CLEANSE_STACK : Z := 16 + RT_STACK.

Definition cleanse_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo D N : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m'
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (D <= a < D + N)) m m'
    /\ bytes_at bsegs m' D (repeat (Z_to_bv 8 0) (Z.to_nat N)) /\ wr_at bsegs m' D N.

Lemma OPENSSL_cleanse_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo D N : Z) (b : block),
  AHEAP Σ OW LB m ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - OPENSSL_CLEANSE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A -> crypto_statics m ->
  In b (OW ++ LB) -> blk_addr b <= D -> D + N <= blk_addr b + blk_size b -> 0 <= N < 2^40 ->
  a0 = wz D -> a1 = wz N ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz OPENSSL_CLEANSE) fc None m (seg_rom bsegs))))
            (ASTA RT Σ PMc (cleanse_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo D N m)).
Proof.
  intros until b. intros HEAP ST CEIL LO SPT SP16 MI -> CS INB BD1 BD2 HN -> ->.
  unfold OPENSSL_CLEANSE_STACK, RT_STACK, OPENSSL_CLEANSE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (AH_range_gen _ _ _ _ b HEAP INB) as (B0 & _ & _ & BC & BI).
  destruct CS as (CS3 & CS4 & CS5 & CS6). unfold CR_MEMSET_FUNC, MEMSET, MallocRep.wz in CS3.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply cps_from_evt'.
  carve_frame 16%nat ST. do 10 step. release_frame FR ST (bv_unsigned sp). step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  apply evt_done.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  pose proof (AH_acc _ _ _ _ b HEAP1 INB) as (WRB & ACCB).
  pose proof (AH_live _ _ _ _ b HEAP1 INB) as INL.
  eapply cps_conseq; [ eapply (MSET Σ PMc) with (d := D) (n := N) (c := Z_to_bv 8 0) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - unfold BnHeapA.ACEIL in *. lia.
  - lia.
  - split; [intros HN0; split; [eapply acc_sub; [exact ACCB | lia | lia] | left; exists (blk_addr b), (blk_size b); split; [exact INL | lia]] |].
    split; [intros i Hi; right; right; left; exists (blk_addr b), (blk_size b); split; [exact INL | lia] |].
    destruct WRB as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi.
    replace (D + i) with (blk_addr b + (D - blk_addr b + i)) by lia. apply W2. lia.
  - exact (AH_art _ _ _ _ HEAP1).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP1 | exact ST | exact CEIL | unfold RT_STACK; lia | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & BZ).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    unfold cleanse_post, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|]. split; [exact (AH_same _ _ _ _ _ HEAP1 ART2)|].
    split.
    { eapply agree_on_trans.
      - eapply agree_on_mono; [exact AG1|]. intros a [Ha _]. exact Ha.
      - pose proof (AH_frames _ _ _ _ HEAP1) as HF1. eapply (AH_agree_ex _ _ _ _ _ _ _ _ _ HEAP1). rewrite <- HF1. exact PRES. }
    split; [exact BZ|]. apply (wr_at_transport bsegs m1 m2 D N); [| exact WM2].
    destruct WRB as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi.
    replace (D + i) with (blk_addr b + (D - blk_addr b + i)) by lia. apply W2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CRYPTO_CLEAR_FREE : Z := 0x1f2c94.
Definition CRYPTO_CLEAR_FREE_STACK : Z := 48 + OPENSSL_CLEANSE_STACK.
Local Notation E_ccf_tail := (E_CRYPTO_clear_free_1f7608 : uk_leaf_tail CRYPTO_CLEAR_FREE).

Lemma CRYPTO_clear_free_walkA : forall {X : Type}
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (p : bptr) (A n num lo : Z) (ras : list Z)
    (k : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop),
  AHEAP Σ OW LB m -> In (p, A, n) OW ->
  stk bsegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - CRYPTO_CLEAR_FREE_STACK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = wz TP_A ->
  crypto_statics m -> 0 <= num <= n -> num < 2^40 -> a0 = wz A -> a1 = wz num ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_CLEAR_FREE (bv_unsigned ra :: ras) ->
  (forall Σ' ms', cfree_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB p lo m Σ' ms' -> implA k Σ' Q ms') ->
  implA (TFree p k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_CLEAR_FREE) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros HEAP IN ST CEIL LO SPT SP16 MI -> CS HNUM HN40 -> -> UW CTX K.
  unfold CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK, CRYPTO_CLEAR_FREE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  assert (INB : In (p, A, n) (OW ++ LB)) by (apply in_or_app; left; exact IN).
  pose proof (AH_range _ _ _ _ p A n HEAP IN) as (A0 & A16 & _ & ACE & AIMG).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  assert (TAIL : forall (m2 : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (jb : list byte),
    AHEAP Σ OW LB m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo (bv_unsigned sp + -48) ->
    rw_cells bsegs m2 (bv_unsigned sp + -48) [CB 8 jb; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    agree_on (aclient_addr (lb_remove p (OW ++ LB)) (bv_unsigned sp)) m m2 ->
    uw_chain USTACK_TOP m2 (bv_unsigned sp) (bv_unsigned s0) ras ->
    implA (TFree p k) Σ Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 TP_A) x5 x6 x7 sp a3 x10 x11 x12 x13 x14 x15 x16 x17 a2 (Z_to_bv 64 A)
               s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F2 (Z_to_bv 64 2043084) fc2 None m2 (seg_rom bsegs))).
  { intros m2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F2 fc2 jb HEAP2 MI2 ST2 FR2 AG2 UW2.
    destruct (GOTC Σ m2 (AH_art _ _ _ _ HEAP2)) as (_ & G2).
    unfold CR_GOT_FREE, CRYPTO_FREE, MallocRep.wz in G2.
    assert (CS2 : crypto_statics m2).
    { eapply crypto_statics_agree; [exact AG2 | | exact CS]. intros a Ha. right; left. exact (ar_LIBW_cs a Ha). }
    destruct CS2 as (_ & _ & CS5 & _). unfold CR_FREE_IMPL, CRYPTO_FREE, MallocRep.wz in CS5.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m2) as MU2. pose proof (wmono_refl bsegs m2) as WM2.
    apply implA_from_evt.
    do 4 step. step. if_true.
    do 6 step. release_frame FR2 ST2 (bv_unsigned sp). step. step.
    apply evt_done.
    assert (INL : In (A, n) (rt_live RT Σ)) by exact (AH_live _ _ _ _ (p, A, n) HEAP2 INB).
    eapply implA_free.
    - eapply cps_conseq; [ eapply (FRE Σ PMc) with (p := A) (n := n) (lo := lo); try reflexivity | intros c Hc; exact Hc
                         | intros c Hc; exact (free_post_R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) ].
      + exact ar_PMc_fdfs.
      + exact ar_PMc_ms.
      + exact INL.
      + exact (AH_art _ _ _ _ HEAP2).
      + exact MI2.
      + rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP2 | exact ST2 | exact CEIL | unfold RT_STACK; lia | unfold USTACK_TOP; lia | exact SP16].
      + eapply unwind_ch_intro with (ras := ras); [exact (uk_ctx_leaf_tail _ _ E_ccf_tail CTX) | exact UW2].
    - intros Σ' ms' (v & m3 & RS & (ART3 & MI3 & ST3) & PRES & LV3 & FR3 & SP3 & CR3).
      apply K. unfold cfree_postA, MallocRep.wz.
      destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
      assert (HEAP3 : AHEAP Σ' (lb_remove p OW) LB m3) by exact (AH_free Σ Σ' OW LB m2 m3 p A n HEAP2 IN ART3 LV3 FR3 SP3).
      do 17 eexists. exists m3. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|].
      split.
      { eapply agree_on_trans; [exact AG2|].
        pose proof HEAP3 as (_ & _ & _ & HL3 & _). pose proof HEAP2 as (_ & _ & HF2 & _ & ND2 & _).
        rewrite (lb_remove_app_l p OW LB ND2) by (apply in_map_iff; exists (p, A, n); split; [reflexivity | exact IN]).
        eapply (AH_agree _ _ _ _ _ _ _ HEAP3). rewrite <- HF2. exact PRES. }
      split; [exact CR3 | exact HEAP3]. }
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply implA_from_evt.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 7 step.
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?EA in K0; lia|]. clear K0.
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply (seg_heap Σ OW LB m m1 _ lo (bv_unsigned sp) HEAP MU WM); [| exact CEIL | unfold USTACK_TOP; lia].
    constructor; [left; cbn; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (OW ++ LB) (bv_unsigned sp) HEAP MU); [| auto].
    constructor; [cbn; unfold BnHeapA.ACEIL in *; lia | constructor]. }
  assert (UW1 : uw_chain USTACK_TOP m1 (bv_unsigned sp) (bv_unsigned s0) ras).
  { eapply uw_chain_munch_nw; [exact UW | exact MU |]. constructor; [cbn; lia | constructor]. }
  step. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    apply evt_done. eapply TAIL; [exact HEAP1 | exact MI | exact ST | exact FR | | exact UW1].
    eapply agree_client_weaken; [exact AG1 | lia | intros b Hb; eapply lb_remove_incl; exact Hb].
  - (* [comment removed for export] *)
    do 2 step.
    apply evt_done.
    eapply implA_step_same.
    + eapply (OPENSSL_cleanse_cpsA) with (b := (p, A, n)) (D := A) (N := num) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
      * exact HEAP1.
      * rewrite ESP. exact ST.
      * exact CEIL.
      * rewrite ESP. unfold OPENSSL_CLEANSE_STACK, RT_STACK. lia.
      * rewrite ESP. unfold USTACK_TOP. lia.
      * rewrite ESP. clear - SP16. Z.div_mod_to_equations. lia.
      * exact MI.
      * eapply crypto_statics_agree; [exact AG1 | | exact CS]. intros a Ha. right; left. exact (ar_LIBW_cs a Ha).
      * exact INB.
      * cbn. lia.
      * lia.
    + intros ms2 PO. unfold cleanse_post in PO. rewrite ?ESP in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & AG2 & BZ & WR2).
      rewrite (ret_pc_even 2043084) by lia.
      eapply TAIL; [exact HEAP2 | exact MI2 | exact ST2 | | | ].
      * eapply (rw_cells_agree _ _ _ _ _ AG2); [exact FR|]. intros a Ha. cbn in Ha. split; [left; unfold USTACK_TOP; lia | unfold BnHeapA.ACEIL in *; lia].
      * eapply agree_on_trans; [eapply agree_client_weaken; [exact AG1 | lia | intros b Hb; eapply lb_remove_incl; exact Hb]|].
        eapply agree_on_mono; [exact AG2|]. intros a Ha. split.
        -- destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; lia | right; left; exact Ha | right; right; exists b; split; [eapply lb_remove_incl; exact Hb | exact Hr]].
        -- intros HAr. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
           ++ unfold BnHeapA.ACEIL in *. lia.
           ++ eapply (blk_not_static Σ OW LB m1 (p, A, n) a HEAP1 IN); [cbn; lia | exact Ha].
           ++ apply lb_remove_In in Hb. destruct Hb as [Hb NE].
              pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) HEAP1 Hb INB NE) as DJ. cbn in DJ. lia.
      * eapply uw_chain_agree; [exact UW1|]. eapply agree_on_mono; [exact AG2|]. intros a Ha. cbv beta in Ha. split; [left; lia | unfold BnHeapA.ACEIL in *; lia].
Qed.

End WithRT.
