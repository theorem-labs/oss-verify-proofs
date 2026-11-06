(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim PEnv APrimSpec2 ASec ASecD AQuar AQuarM AQuarR AHeap ALedger ALinkPg ALinkVm ALink ALinkFreeIn AHeap2 AHeapB AMallocP AVaOf.
Import ListNotations.
Open Scope Z_scope.

Definition sec_mz (chs : list qchunk) : Z := fold_right (fun ch acc => match qc_kind ch with QSec sc => sc_msize sc | QPrim _ _ => 0 end + acc) 0 chs.
Definition sec_nz (chs : list qchunk) : Z := fold_right (fun ch acc => match qc_kind ch with QSec _ => qc_n ch | QPrim _ _ => 0 end + acc) 0 chs.
Definition sec_cz (chs : list qchunk) : Z := Z.of_nat (length (flat_map sec_of chs)).

Lemma sec_mz_app : forall l1 l2, sec_mz (l1 ++ l2) = sec_mz l1 + sec_mz l2.
Proof. induction l1 as [|x l1 IH]; intros l2; [reflexivity|]. cbn [sec_mz fold_right app]. fold (sec_mz (l1 ++ l2)). fold (sec_mz l1). rewrite IH. lia. Qed.
Lemma sec_cz_app : forall l1 l2, sec_cz (l1 ++ l2) = sec_cz l1 + sec_cz l2.
Proof. intros l1 l2. unfold sec_cz. rewrite flat_map_app, length_app, Nat2Z.inj_add. reflexivity. Qed.

Lemma sec_mz_le : forall chs, Forall ch_cls_ok chs -> sec_mz chs <= sec_nz chs + 16384 * sec_cz chs.
Proof.
  induction chs as [|ch chs IH]; intros FC; [unfold sec_mz, sec_nz, sec_cz; cbn; lia|]. apply Forall_cons_iff in FC as [CK FC]. specialize (IH FC).
  unfold sec_cz in *. cbn [sec_mz sec_nz fold_right flat_map]. fold (sec_mz chs). fold (sec_nz chs). rewrite length_app, Nat2Z.inj_add.
  unfold ch_cls_ok in CK. unfold sec_of at 1. destruct (qc_kind ch) as [c v|sc]; cbn [length Z.of_nat]; [lia|]. destruct CK as [_ CK]. lia.
Qed.
Lemma sec_nz_wsum : forall chs, Forall qchunk_wf chs -> 0 <= sec_nz chs <= wsum chs.
Proof.
  induction chs as [|ch chs IH]; intros FW; [unfold sec_nz, wsum; cbn; lia|]. apply Forall_cons_iff in FW as [(_ & _ & N1 & _) FW]. specialize (IH FW).
  cbn [sec_nz wsum fold_right]. fold (sec_nz chs). fold (wsum chs). destruct (qc_kind ch); lia.
Qed.

Definition sec_w (l : list schunk) : Z := fold_right (fun sc acc => sc_msize sc + (sc_msize sc / 8 + 8192) + acc) 0 l.
Definition sec_m (l : list schunk) : Z := fold_right (fun sc acc => sc_msize sc + acc) 0 l.
Lemma sec_w_le : forall l, Forall (fun sc => 0 <= sc_msize sc) l -> sec_w l <= sec_m l + sec_m l / 8 + 8192 * Z.of_nat (length l) /\ 0 <= sec_m l.
Proof.
  induction l as [|sc l IH]; intros F; [unfold sec_w, sec_m; cbn; lia|]. apply Forall_cons_iff in F as [F1 F]. destruct (IH F) as [IH1 IH2].
  cbn [sec_w sec_m fold_right length]. fold (sec_w l). fold (sec_m l). rewrite Nat2Z.inj_succ. split; [| lia]. Z.div_mod_to_equations. lia.
Qed.
Lemma sec_m_mz : forall chs, sec_m (flat_map sec_of chs) = sec_mz chs.
Proof.
  induction chs as [|ch chs IH]; [reflexivity|]. cbn [flat_map sec_mz fold_right]. fold (sec_mz chs). rewrite <- IH. unfold sec_of at 1.
  destruct (qc_kind ch); cbn [app sec_m fold_right]; reflexivity.
Qed.
Lemma sec_m_perm : forall l l', Permutation l l' -> sec_m l = sec_m l'.
Proof. intros l l' PM. induction PM; cbn [sec_m fold_right]; try fold (sec_m l); try fold (sec_m l'); lia. Qed.

Section US.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).

#[using="Type"] Lemma chunks_weight_le : forall l, Forall (chunk_ok AL) l -> chunks_weight (map cpair l) <= sec_w l.
Proof.
  induction l as [|sc l IH]; intros F; [unfold chunks_weight, sec_w; cbn; lia|]. apply Forall_cons_iff in F as [CK F]. specialize (IH F).
  cbn [map chunks_weight fold_right sec_w]. fold (chunks_weight (map cpair l)). fold (sec_w l). unfold cpair at 1 2 3. cbn [fst snd].
  pose proof (chunk_ok_msize AL sc CK) as (CM1 & _). destruct CK as (_ & CK2 & _).
  pose proof (hull_bytes_bound (sc_beg sc) (sc_msize sc) ltac:(lia) ltac:(lia)) as HB. unfold page_size in HB. lia.
Qed.

Definition SUM_PM : Z := fold_right Z.add 0 (map (fun i => PM (Z.of_nat i)) (seq 1 31)).
#[using="Type"] Lemma sum_mu_le_pm : forall P, (forall c, 1 <= c <= 31 -> p_mu (get_cls P c) <= PM c) -> sum_mu P <= SUM_PM.
Proof.
  intros P BD. unfold sum_mu, SUM_PM.
  assert (G : forall l : list nat, (forall i, In i l -> (1 <= i <= 31)%nat) ->
            fold_right Z.add 0 (map (fun i => p_mu (get_cls P (Z.of_nat i))) l) <= fold_right Z.add 0 (map (fun i => PM (Z.of_nat i)) l)).
  { induction l as [|i l IH]; intros HI; [cbn; lia|]. cbn [map fold_right].
    pose proof (BD (Z.of_nat i) ltac:(pose proof (HI i (or_introl eq_refl)); lia)). specialize (IH (fun j Hj => HI j (or_intror Hj))). lia. }
  apply G. intros i Hi. apply in_seq in Hi. lia.
Qed.

#[using="Type"] Theorem used_components : forall s LB (m : mem), RHEAP_B AL E s LB m -> mem_inv asegs m ->
  let v := va_of s in let P := bs_prim s in
  let CS := sec_live_cnt s + A0_QB / 64521 in
  let MS := sec_live_bytes s + A0_QB + 16384 * CS in
  va_prim v = sum_mu P + sum_mfa P /\ sum_mu P <= SUM_PM /\ 0 <= sum_mfa P <= 31 * K_FA_SIZE
  /\ chunks_weight (va_chunks v) <= MS + MS / 8 + 8192 * CS
  /\ va_nsec v = bs_nsec s /\ 0 <= va_aux v <= 64 * 155648.
Proof.
  intros s LB m HR MI. cbv zeta.
  pose proof (rheap_qbytes AL E s LB m HR) as [FWG QB].
  pose proof HR as (PLB & LOK & _ & INVB & _ & _ & _ & _ & _ & _ & _ & _ & WFL & _ & _ & PSEC & _ & _ & _ & _ & _ & _ & CCL & CCQ & _ & BUD & _).
  pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (RP & _ & RS & _ & _ & _ & _ & WFQ & _).
  destruct (clear_ctx AL (bs_X s) m RP RS) as (WF0 & SOK & _). pose proof RS as ((W0a & _ & W0b & _) & _).
  destruct BUD as (BMU & _).
  split; [reflexivity|].
  split; [exact (sum_mu_le_pm (bs_prim s) BMU)|].
  split; [exact (sum_mfa_bound (bs_prim s) WF0)|].
  split.
  { unfold va_of. cbn [va_chunks].
    set (Qc := flat_map qb_chunks (bs_gl s)) in *. set (Lc := live_chunks s) in *.
    pose proof (chunks_weight_le _ SOK) as CW. cbn [bs_X snd] in CW.
    assert (F0 : Forall (fun sc => 0 <= sc_msize sc) (se_chunks (bs_sec s))).
    { eapply Forall_impl; [| exact SOK]. intros sc CK. pose proof (chunk_ok_msize AL sc CK). lia. }
    destruct (sec_w_le _ F0) as [SW _].
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
    lia. }
  split; [reflexivity|].
  unfold va_of, aux_of. cbn [va_aux]. change (131072 + 131072 / 8 + 2 * 4096) with 155648.
  assert (Q64 : 0 <= se_nres (bs_sec s) / 16384 <= 64) by (clear - W0a W0b; cbn [bs_X snd] in *; Z.div_mod_to_equations; lia).
  lia.
Qed.

#[using="Type"] Lemma SUM_PM_val : SUM_PM = 59635400704.
Proof. vm_compute. reflexivity. Qed.

Definition used (v : vabs) : Z := va_prim v + va_prim v / 8 + chunks_weight (va_chunks v) + 8192 * va_nsec v + va_aux v.
Definition U_STATIC : Z := 533915238400.

#[using="Type"] Theorem rheap_used_static : forall s LB (m : mem), RHEAP_B AL E s LB m -> mem_inv asegs m -> used (va_of s) <= U_STATIC.
Proof.
  intros s LB m HR MI. destruct (used_components s LB m HR MI) as (EP & MU & (MF0 & MF) & CW & EN & (AX0 & AX)). cbv zeta in *.
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & SC0 & SB0 & NS0) & _).
  unfold used. rewrite EP, EN. rewrite SUM_PM_val in MU.
  assert (SCN : 0 <= sec_live_cnt s) by (unfold sec_live_cnt; lia).
  set (CSx := sec_live_cnt s + A0_QB / 64521) in *. set (MSx := sec_live_bytes s + A0_QB + 16384 * CSx) in *.
  assert (QV : A0_QB / 64521 = 4176) by (vm_compute; reflexivity).
  assert (C1 : CSx <= 16384 + 4176) by (unfold CSx, A0_SEC_CNT in *; lia).
  assert (M1 : MSx <= 2147483648 + 269484032 + 16384 * (16384 + 4176)) by (unfold MSx, A0_SEC_BYTES, A0_QB in *; lia).
  assert (D1 : MSx / 8 <= (2147483648 + 269484032 + 16384 * (16384 + 4176)) / 8) by (apply Z.div_le_mono; lia).
  assert (P1 : sum_mu (bs_prim s) + sum_mfa (bs_prim s) <= 59635400704 + 31 * 536870912) by (change K_FA_SIZE with 536870912 in MF; lia).
  assert (P8 : (sum_mu (bs_prim s) + sum_mfa (bs_prim s)) / 8 <= (59635400704 + 31 * 536870912) / 8) by (apply Z.div_le_mono; lia).
  unfold U_STATIC, A0_NSEC_MAX in *.
  change ((59635400704 + 31 * 536870912) / 8) with 9534799872 in P8.
  change ((2147483648 + 269484032 + 16384 * (16384 + 4176)) / 8) with 344227840 in D1.
  lia.
Qed.

#[using="Type"] Lemma vroom_of_static : forall (Bs : vmbase) s LB (m : mem) e, RHEAP_B AL E s LB m -> mem_inv asegs m ->
  vb_used Bs + U_STATIC + e <= target_alloc_limit -> vroom Bs (va_of s) e.
Proof. intros Bs s LB m e HR MI CL. pose proof (rheap_used_static s LB m HR MI) as U. unfold used in U. unfold vroom. lia. Qed.
End US.
