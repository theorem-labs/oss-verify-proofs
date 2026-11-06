(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim PEnv APrimSpec2 APrimLem APrimPop APrimRefill ASec ASecD AQuar AQuarM AQuarR AHeap ALedger ALinkPg ALinkVm ALink ALinkPrim ALinkSec
                        F_quar_E F_quar_P ALinkFree ALinkFreeIn AHeap2 AHeapB AMallocP AVaOf AVaOfM AUsedStatic APureInv.
Import ListNotations.
Open Scope Z_scope.

Definition rest (v : vabs) : Z := chunks_weight (va_chunks v) + 8192 * va_nsec v + va_aux v.
Definition PMAX : Z := 76278398976.
Definition REST_MAX : Z := 448102039552.
Definition MS_MAX : Z := 2753822720.
Definition CS_MAX : Z := 20560.

Lemma chunks_bytes_cpair : forall l, chunks_bytes (map cpair l) = sec_m l.
Proof. induction l as [|sc l IH]; [reflexivity|]. cbn [map chunks_bytes fold_right sec_m]. fold (chunks_bytes (map cpair l)). fold (sec_m l). rewrite IH. reflexivity. Qed.

Section ROOM.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv) (Bs : vmbase).
Hypothesis VBU : vb_used Bs = 2477351424.
Hypothesis VBG : vb_gapB Bs = 137478443008.
Hypothesis VBN : vb_gapN Bs = 16.

#[using="Type"] Lemma sec_components : forall s LB (m : mem), RHEAP_B AL E s LB m ->
  let CS := sec_live_cnt s + A0_QB / 64521 in
  let MS := sec_live_bytes s + A0_QB + 16384 * CS in
  0 <= sec_m (se_chunks (bs_sec s)) <= MS /\ Z.of_nat (length (se_chunks (bs_sec s))) <= CS
  /\ chunks_weight (map cpair (se_chunks (bs_sec s))) <= MS + MS / 8 + 8192 * CS
  /\ 0 <= sec_live_cnt s <= A0_SEC_CNT /\ sec_live_bytes s <= A0_SEC_BYTES /\ 0 <= bs_nsec s <= A0_NSEC_MAX
  /\ 0 <= aux_of (bs_sec s) <= 64 * 155648.
Proof.
  intros s LB m HR. cbv zeta.
  pose proof (rheap_qbytes AL E s LB m HR) as [FWG QB].
  pose proof HR as (PLB & LOK & _ & INVB & _ & _ & _ & _ & _ & _ & _ & _ & WFL & _ & _ & PSEC & _ & _ & _ & _ & _ & _ & CCL & CCQ & _ & BUD & _).
  destruct INVB as (RP & _ & RS & _ & _ & _ & WFQ & _).
  destruct (clear_ctx AL (bs_X s) m RP RS) as (WF0 & SOK & _). pose proof RS as ((W0a & _ & W0b & _) & _).
  destruct BUD as (_ & _ & _ & _ & SC0 & SB0 & NS0).
  set (Qc := flat_map qb_chunks (bs_gl s)) in *. set (Lc := live_chunks s) in *.
  pose proof (chunks_weight_le AL _ SOK) as CW. cbn [bs_X snd] in CW.
  assert (F0 : Forall (fun sc => 0 <= sc_msize sc) (se_chunks (bs_sec s))).
  { eapply Forall_impl; [| exact SOK]. intros sc CK. pose proof (chunk_ok_msize AL sc CK). lia. }
  destruct (sec_w_le _ F0) as [SW SM0].
  assert (EM : sec_m (se_chunks (bs_sec s)) = sec_mz Qc + sec_mz Lc).
  { rewrite (sec_m_perm _ _ PSEC), <- flat_map_app, sec_m_mz, sec_mz_app. reflexivity. }
  assert (EL : Z.of_nat (length (se_chunks (bs_sec s))) = sec_cz Qc + sec_cz Lc).
  { rewrite (Permutation_length PSEC), <- flat_map_app. fold (sec_cz (Qc ++ Lc)). apply sec_cz_app. }
  pose proof (sec_mz_le Qc CCQ) as MQ. pose proof (sec_mz_le Lc CCL) as ML.
  pose proof (sec_nz_wsum Qc WFQ) as [_ NQ]. pose proof (wsum_list _ FWG) as WL. fold Qc in WL.
  pose proof (sec_cnt_quar Qc WFQ CCQ) as CQ. fold (sec_cz Qc) in CQ.
  assert (CQ' : 0 <= sec_cz Qc <= A0_QB / 64521) by (split; [unfold sec_cz; lia| apply Z.div_le_lower_bound; lia]).
  assert (NL : sec_nz Lc = sec_live_bytes s).
  { unfold Lc, live_chunks, sec_live_bytes. clear - LOK CCL WFL. unfold live_chunks in *.
    induction (bs_live s) as [|[ch cn] l IH]; [reflexivity|].
    apply Forall_cons_iff in LOK as [L1 LOK]. cbn [map fst] in CCL, WFL. apply Forall_cons_iff in CCL as [C1 CCL]. apply Forall_cons_iff in WFL as [(_ & _ & N1 & _) WFL].
    cbn [map sec_nz fold_right]. fold (sec_nz (map fst l)). rewrite (IH LOK WFL CCL). unfold sec_rec_bytes. cbn [fst snd].
    cbn [fst snd] in C1, N1. unfold ch_cls_ok in C1. destruct (qc_kind ch) as [c v|sc] eqn:EKc; [reflexivity|]. destruct C1 as [C1 _].
    pose proof (a0_cls0_min (qc_n ch) ltac:(lia) C1). destruct L1 as [L1|[_ L1]]; cbn [fst snd] in L1; lia. }
  assert (ECL : sec_cz Lc = sec_live_cnt s) by reflexivity.
  rewrite EM, EL in SW. rewrite NL, ECL in *.
  assert (SCN : 0 <= sec_live_cnt s) by (unfold sec_live_cnt; lia).
  set (M0 := sec_mz Qc + sec_mz Lc) in *. set (MS := sec_live_bytes s + A0_QB + 16384 * (sec_live_cnt s + A0_QB / 64521)).
  assert (MM : M0 <= MS) by (unfold M0, MS; lia).
  assert (DM : M0 / 8 <= MS / 8) by (apply Z.div_le_mono; lia).
  split; [rewrite EM; fold M0; split; [rewrite EM in SM0; exact SM0| exact MM]|]. split; [rewrite EL; lia|]. split; [lia|].
  split; [split; [exact SCN| exact SC0]|]. split; [exact SB0|]. split; [exact NS0|].
  unfold aux_of. change (131072 + 131072 / 8 + 2 * 4096) with 155648.
  assert (Q64 : 0 <= se_nres (bs_sec s) / 16384 <= 64) by (clear - W0a W0b; cbn [bs_X snd] in *; Z.div_mod_to_equations; lia).
  lia.
Qed.

#[using="Type"] Lemma prim_components : forall s, pure_inv AL s ->
  sum_mu (bs_prim s) <= SUM_PM /\ 0 <= sum_mfa (bs_prim s) <= 31 * K_FA_SIZE /\ 0 <= sum_mu (bs_prim s).
Proof.
  intros s (_ & WF0 & (BMU & _) & _). split; [exact (sum_mu_le_pm (bs_prim s) BMU)|]. split; [exact (sum_mfa_bound (bs_prim s) WF0)|].
  pose proof (sum_mu_bound (bs_prim s) FA_OFF ltac:(lia)) as SB.
  assert (BD : forall c, 1 <= c <= 31 -> 0 <= p_mu (get_cls (bs_prim s) c) <= FA_OFF).
  { intros c Hc. pose proof (WF0 c Hc) as (_ & _ & _ & _ & _ & _ & AU & MUF & _). lia. }
  specialize (SB BD). lia.
Qed.

#[using="Type"] Lemma rest_le : forall s LB (m : mem), RHEAP_B AL E s LB m -> rest (va_of s) <= REST_MAX.
Proof.
  intros s LB m HR. destruct (sec_components s LB m HR) as (_ & _ & CW & (SC0 & SC1) & SB1 & (NS0 & NS1) & (AX0 & AX1)). cbv zeta in CW.
  unfold rest, va_of. cbn [va_chunks va_nsec va_aux].
  assert (QV : A0_QB / 64521 = 4176) by (vm_compute; reflexivity). rewrite QV in CW.
  set (CSx := sec_live_cnt s + 4176) in *. set (MSx := sec_live_bytes s + A0_QB + 16384 * CSx) in *.
  assert (C1 : CSx <= 20560) by (unfold CSx, A0_SEC_CNT in *; lia).
  assert (M1 : MSx <= 2753822720) by (unfold MSx, A0_SEC_BYTES, A0_QB in *; lia).
  assert (D1 : MSx / 8 <= 2753822720 / 8) by (apply Z.div_le_mono; lia). change (2753822720 / 8) with 344227840 in D1.
  unfold REST_MAX, A0_NSEC_MAX in *. lia.
Qed.

#[using="Type"] Lemma rest_sec_le : forall s LB (m : mem) n nm, RHEAP_B AL E s LB m ->
  sec_live_cnt s + 1 <= A0_SEC_CNT -> sec_live_bytes s + n <= A0_SEC_BYTES -> bs_nsec s + 1 <= A0_NSEC_MAX -> 0 <= nm <= n + 16384 ->
  chunks_weight (va_chunks (va_of s)) + (nm + (nm / 8 + 2 * page_size)) + 8192 * (bs_nsec s + 1) + 64 * 155648 <= REST_MAX
  /\ chunks_bytes (va_chunks (va_of s)) + nm <= MS_MAX /\ Z.of_nat (length (va_chunks (va_of s))) + 1 <= CS_MAX /\ 0 <= chunks_bytes (va_chunks (va_of s)).
Proof.
  intros s LB m n nm HR BC BB BN NM. destruct (sec_components s LB m HR) as ((SM0 & SM1) & SL & CW & (SC0 & SC1) & SB1 & (NS0 & NS1) & (AX0 & AX1)). cbv zeta in SM1, SL, CW.
  unfold va_of. cbn [va_chunks]. rewrite chunks_bytes_cpair, length_map.
  assert (QV : A0_QB / 64521 = 4176) by (vm_compute; reflexivity). rewrite QV in *.
  set (CSx := sec_live_cnt s + 4176) in *. set (MSx := sec_live_bytes s + A0_QB + 16384 * CSx) in *.
  assert (C1 : CSx + 1 <= 20560) by (unfold CSx, A0_SEC_CNT in *; lia).
  assert (M1 : MSx + nm <= 2753822720) by (unfold MSx, A0_SEC_BYTES, A0_QB in *; lia).
  assert (D1 : MSx / 8 + nm / 8 <= 2753822720 / 8) by (etransitivity; [| apply (Z.div_le_mono (MSx + nm) 2753822720 8); lia]; clear; Z.div_mod_to_equations; lia).
  change (2753822720 / 8) with 344227840 in D1.
  unfold REST_MAX, MS_MAX, CS_MAX, A0_NSEC_MAX, page_size in *. split; [lia|]. split; [lia|]. split; lia.
Qed.

#[using="VBU"] Lemma vroom_prim_gen : forall v d e, va_prim v + d <= PMAX -> rest v <= REST_MAX -> e <= 1048576 ->
  vroom Bs v (d + d / 8 + e).
Proof.
  intros v d e PD RS EE. unfold vroom. unfold rest in RS. rewrite VBU.
  assert (D8 : va_prim v / 8 + d / 8 <= PMAX / 8) by (etransitivity; [| apply (Z.div_le_mono (va_prim v + d) PMAX 8); lia]; clear; Z.div_mod_to_equations; lia).
  change (PMAX / 8) with 9534799872 in D8. unfold PMAX, REST_MAX in *. change target_alloc_limit with 549755813888. lia.
Qed.

#[using="VBU"] Lemma room_refill : forall s v c, pure_inv AL s -> 1 <= c <= 31 -> p_cnt (get_cls (bs_prim s) c) = 0 ->
  va_prim v = sum_mu (bs_prim s) + sum_mfa (bs_prim s) -> rest v <= REST_MAX ->
  let D := D_gfa (get_cls (bs_prim s) c) c (max_count c / 2) in
  vroom Bs v (D + D / 8 + 4 * page_size).
Proof.
  intros s v c PIV Hc C0 EP RS. cbv zeta.
  destruct (prim_components s PIV) as (MU & (MF0 & MF) & MU0).
  pose proof PIV as ((LEN & _) & WF0 & (BMU & _) & _). cbn [bs_X fst] in LEN.
  pose proof (pure_refill_budget AL s PIV c Hc) as RB. pose proof (pure_refill_mu AL s PIV c Hc C0) as RM.
  pose proof (cache_alloc_sums (bs_prim s) c Hc LEN) as CS. unfold D_calloc in CS. rewrite (proj2 (Z.eqb_eq _ _) C0) in CS.
  pose proof (pwf_cache_alloc (bs_prim s) c Hc LEN WF0 (fun _ => RB)) as WF1.
  destruct (cache_alloc_mu (bs_prim s) c Hc LEN) as (EO & EMU & _). cbv zeta in EO, EMU. rewrite (proj2 (Z.eqb_eq _ _) C0) in EMU.
  assert (MU1 : sum_mu (fst (cache_alloc (bs_prim s) c)) <= SUM_PM).
  { apply sum_mu_le_pm. intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite EMU; exact RM| rewrite (EO c' Hc' NE); exact (BMU c' Hc')]. }
  pose proof (sum_mfa_bound _ WF1) as [_ MF1]. rewrite SUM_PM_val in *. change K_FA_SIZE with 536870912 in *.
  set (D := D_gfa (get_cls (bs_prim s) c) c (max_count c / 2)) in *.
  apply vroom_prim_gen; [unfold PMAX; lia| exact RS| unfold page_size; lia].
Qed.

#[using="VBU"] Lemma room_free : forall s v ch, pure_inv AL s ->
  va_prim v = sum_mu (bs_prim s) + sum_mfa (bs_prim s) -> rest v <= REST_MAX ->
  let P := bs_prim s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
  let X1 := (fst (enq_prim P loc), bs_sec s) in let todo := put_todo P glob loc ch in
  8 * R_dorecycle X1 todo <= 9 * (31 * K_FA_SIZE - sum_mfa (fst X1)) ->
  (enq_refills P loc = true -> vroom Bs v (D_enq P loc + D_enq P loc / 8 + 4 * page_size))
  /\ vroom Bs (va_enq v P loc) (R_dorecycle X1 todo + 2 * page_size).
Proof.
  intros s v ch PIV EP RS. cbv zeta. intros RB.
  pose proof PIV as ((LEN & _) & WF0 & (BMU & _) & _). cbn [bs_X fst] in LEN.
  pose proof (pure_refill_budget AL s PIV K_BCLASS ltac:(lia)) as RB24.
  set (P := bs_prim s) in *. set (loc := q_loc (bs_quar s)) in *. set (PN := fst (enq_prim P loc)) in *.
  pose proof (D_enq_eq P loc LEN) as DE. fold PN in DE.
  destruct (enq_mu P loc LEN) as (EO & E24 & _). cbv zeta in EO, E24. fold PN in EO, E24.
  assert (MU1 : sum_mu PN <= SUM_PM).
  { apply sum_mu_le_pm. intros c' Hc'. destruct (Z.eq_dec c' K_BCLASS) as [->|NE]; [| rewrite (EO c' Hc' NE); exact (BMU c' Hc')].
    rewrite E24. destruct (enq_refills P loc) eqn:ER; [| exact (BMU K_BCLASS ltac:(lia))].
    unfold enq_refills in ER. apply andb_true_iff in ER as [_ ER]. apply Z.eqb_eq in ER.
    exact (pure_refill_mu AL s PIV K_BCLASS ltac:(lia) ER). }
  pose proof (pwf_enq P loc LEN WF0 (fun _ => RB24)) as WF1. fold PN in WF1.
  pose proof (sum_mfa_bound _ WF1) as [MF0 MF1]. rewrite SUM_PM_val in *. change K_FA_SIZE with 536870912 in *. cbn [fst] in RB. fold PN in RB.
  split.
  - intros _. apply vroom_prim_gen; [unfold PMAX; lia| exact RS| unfold page_size; lia].
  - unfold vroom, va_enq. cbn [va_prim va_chunks va_nsec va_aux]. unfold rest in RS. rewrite VBU.
    set (R := R_dorecycle (PN, bs_sec s) (put_todo P (q_glob (bs_quar s)) loc ch)) in *.
    set (T := va_prim v + D_enq P loc) in *. assert (ET : T = sum_mu PN + sum_mfa PN) by (unfold T; lia).
    assert (T8 : 8 * (T / 8) <= T) by (clear; Z.div_mod_to_equations; lia).
    unfold REST_MAX, page_size in *. change target_alloc_limit with 549755813888. lia.
Qed.

#[using="VBU VBG VBN"] Lemma room_sec : forall s LB (m : mem) n nm, RHEAP_B AL E s LB m ->
  sec_live_cnt s + 1 <= A0_SEC_CNT -> sec_live_bytes s + n <= A0_SEC_BYTES -> bs_nsec s + 1 <= A0_NSEC_MAX -> 0 <= nm <= n + 16384 -> n <= A0_MAXREQ ->
  vroom Bs (va_of s) (nm + (nm / 8 + 2 * page_size) + 8192 + parr_step_cost) /\ gap_room Bs (va_of s) nm.
Proof.
  intros s LB m n nm HR BC BB BN NM NR.
  destruct (rest_sec_le s LB m n nm HR BC BB BN NM) as (R1 & CB & CL & CB0).
  destruct (sec_components s LB m HR) as (_ & _ & _ & _ & _ & _ & (AX0 & AX1)).
  destruct (prim_components s (pure_inv_of_rheap AL E s LB m HR)) as (MU & (MF0 & MF) & MU0). rewrite SUM_PM_val in MU. change K_FA_SIZE with 536870912 in MF.
  split.
  - unfold vroom. rewrite VBU. unfold va_of in *. cbn [va_prim va_chunks va_nsec va_aux] in *.
    set (T := sum_mu (bs_prim s) + sum_mfa (bs_prim s)) in *.
    assert (T8 : T / 8 <= 76278398976 / 8) by (apply Z.div_le_mono; lia). change (76278398976 / 8) with 9534799872 in T8.
    unfold REST_MAX, parr_step_cost, page_size in *. change target_alloc_limit with 549755813888. lia.
  - unfold gap_room. rewrite VBG, VBN. pose proof alloc_ceiling_range as ACR. unfold alloc_floor in ACR.
    set (L := Z.of_nat (length (va_chunks (va_of s)))) in *. assert (L0 : 0 <= L) by (unfold L; lia).
    unfold A0_MAXREQ in NR. change (2^28) with 268435456 in NR.
    assert (PR : L * (nm + 4095) <= 20560 * 268455935) by (apply Z.mul_le_mono_nonneg; unfold CS_MAX in *; lia).
    unfold MS_MAX in *. lia.
Qed.

#[using="Type"] Lemma rest_after_sec : forall s LB (m : mem) n a size s1, RHEAP_B AL E s LB m ->
  sec_live_cnt s + 1 <= A0_SEC_CNT -> sec_live_bytes s + n <= A0_SEC_BYTES -> bs_nsec s + 1 <= A0_NSEC_MAX -> sec_msize size <= n + 16384 ->
  sec_wf AL (sec_alloc (bs_sec s) a size) -> 0 <= a ->
  bs_sec s1 = sec_alloc (bs_sec s) a size -> bs_nsec s1 = bs_nsec s + 1 -> rest (va_of s1) <= REST_MAX.
Proof.
  intros s LB m n a size s1 HR BC BB BN NM SWF A0 ES EN.
  pose proof SWF as (W0 & _ & W2 & _ & _ & COK & _). apply Forall_app in COK as [_ COK]. apply Forall_cons_iff in COK as [CK _].
  pose proof (chunk_ok_msize AL _ CK) as [M1 _]. cbn [sc_msize] in M1.
  destruct (rest_sec_le s LB m n (sec_msize size) HR BC BB BN ltac:(lia)) as (R1 & _).
  unfold rest, va_of. cbn [va_chunks va_nsec va_aux]. rewrite ES, EN.
  assert (ECW : chunks_weight (map cpair (se_chunks (sec_alloc (bs_sec s) a size)))
                = sec_msize size + hull_bytes a (sec_msize size) + chunks_weight (map cpair (se_chunks (bs_sec s)))).
  { unfold sec_alloc. cbn [se_chunks]. rewrite map_app. cbn [map]. unfold cpair at 2. cbn [sc_beg sc_msize].
    rewrite <- (chunks_weight_perm _ _ (Permutation_cons_append (map cpair (se_chunks (bs_sec s))) (a, sec_msize size))). reflexivity. }
  rewrite ECW. pose proof (hull_bytes_bound a (sec_msize size) A0 ltac:(lia)) as [_ HB].
  assert (AX : aux_of (sec_alloc (bs_sec s) a size) <= 64 * 155648).
  { unfold aux_of. change (131072 + 131072 / 8 + 2 * 4096) with 155648. change (2^23) with 8388608 in W2.
    assert (Q64 : se_nres (sec_alloc (bs_sec s) a size) / 16384 <= 64) by (clear - W0 W2; Z.div_mod_to_equations; lia). lia. }
  unfold va_of in R1. cbn [va_chunks] in R1. lia.
Qed.
End ROOM.
