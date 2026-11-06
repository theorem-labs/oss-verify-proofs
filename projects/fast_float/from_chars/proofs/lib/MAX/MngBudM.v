(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import AllocNodesCfg PlacementCount.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU MngMeas MngWk MngRz2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMeas OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRz2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition rk_meta (rg : region) : bool := match rg_kind rg with RkMetaRes => true | _ => false end.

Lemma ropen_isum : forall rs k, ropen rs = isum (fun _ rg => if rk_meta rg then Z.of_nat (length (rg_rw rg)) else 0) k rs.
Proof.
  induction rs as [|rg rs IH]; intros k; [reflexivity|]. cbn [isum]. rewrite <- (IH (S k)).
  unfold ropen, rk_meta. cbn [fold_right]. destruct (rg_kind rg); reflexivity.
Qed.

Lemma rtot_isum : forall rs k, rtot rs = isum (fun _ rg => if rk_meta rg then rg_len rg else 0) k rs.
Proof.
  induction rs as [|rg rs IH]; intros k; [reflexivity|]. cbn [isum]. rewrite <- (IH (S k)).
  unfold rtot, rk_meta. cbn [fold_right]. destruct (rg_kind rg); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pages_apart : forall B o1 o2 z, o1 mod PGSZ = 0 -> o2 mod PGSZ = 0 -> o1 <> o2 ->
  B + o1 <= z < B + o1 + PGSZ -> ~ (B + o2 <= z < B + o2 + PGSZ).
Proof.
  intros B o1 o2 z H1 H2 Hne Hz Hz2. unfold PGSZ in *.
  pose proof (Z.div_mod o1 4096 ltac:(lia)) as Q1. pose proof (Z.div_mod o2 4096 ltac:(lia)) as Q2.
  rewrite H1, Z.add_0_r in Q1. rewrite H2, Z.add_0_r in Q2.
  assert (o1 / 4096 <> o2 / 4096) by (intros E; apply Hne; lia). lia.
Qed.

Section Meas.
Variables (HTOP : Z) (FORB : list (Z * Z)) (L : layout) (x : kf) (md : Model).
Hypothesis HL : LINK HTOP FORB L x md.

#[using="HTOP FORB L x HL"] Lemma maps_inrange : inrange (vm_maps (m_vmmaps md)).
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL : LiaFast.U) => LiaFast.u0).
  intros e He. pose proof (lk_mtop _ _ _ _ _ HL e He). pose proof (alloc_top_lt (m_vmmaps md)). unfold two_pow_64 in *. lia.
Qed.

#[using="HTOP FORB L x HL"] Lemma backed_le : Wt (vm_maps (m_vmmaps md)) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1)) <= vm_backing_used md.
Proof. LiaFast.lf_pins (fun (HTOP FORB L x HL : LiaFast.U) => LiaFast.u0).
  unfold vm_backing_used. rewrite (lk_lazy _ _ _ _ _ HL). cbn [maps_subtract_all]. unfold vm_backed_maps.
  rewrite live_bytes_Wt, (msa_Wt _ _ _ maps_inrange). pose proof (Nat2Z.is_nonneg (length (m_vm_materialized md))).
  unfold page_size. lia.
Qed.

(* [comment removed for export] *)
#[using="HTOP FORB L md HL"] Lemma rgeo_len : forall r rg, nth_error (kf_regions x) r = Some rg -> rg_live rg = true -> PGSZ <= rg_len rg.
Proof. LiaFast.lf_pins (fun (HTOP FORB L md HL : LiaFast.U) => LiaFast.u0).
  intros r rg H1 H2. destruct (lk_rgeo _ _ _ _ _ HL r rg H1 H2) as (_ & _ & G3 & G4 & _). unfold PGSZ in *.
  pose proof (Z.div_mod (rg_len rg) 4096 ltac:(lia)) as Q. rewrite G4, Z.add_0_r in Q.
  assert (0 < rg_len rg / 4096) by (apply Z.div_str_pos; lia). lia.
Qed.

#[using="HTOP FORB md HL"] Lemma two_regions : forall r1 r2 rg1 rg2 z, nth_error (kf_regions x) r1 = Some rg1 -> nth_error (kf_regions x) r2 = Some rg2 ->
  rg_live rg1 = true -> rg_live rg2 = true ->
  ly_reg L r1 <= z < ly_reg L r1 + rg_len rg1 -> ly_reg L r2 <= z < ly_reg L r2 + rg_len rg2 -> r1 = r2.
Proof. LiaFast.lf_pins (fun (HTOP FORB md HL : LiaFast.U) => LiaFast.u0).
  intros r1 r2 rg1 rg2 z H1 H2 L1 L2 Z1 Z2. destruct (Nat.eq_dec r1 r2) as [E|Hne]; [exact E|].
  pose proof (lk_rdisj _ _ _ _ _ HL r1 r2 rg1 rg2 Hne H1 H2 L1 L2) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

(* [comment removed for export] *)

Definition OPF (z : Z) : Z :=
  isum (fun r rg => if rk_meta rg && rg_live rg then lsum (fun o => ind (inI (ly_reg L r + o) (ly_reg L r + o + PGSZ) z)) (rg_rw rg) else 0)
       0 (kf_regions x).

(* [comment removed for export] *)
#[using="HTOP FORB md HL"] Lemma page_term_zero : forall r rg z, nth_error (kf_regions x) r = Some rg -> rk_meta rg = true -> rg_live rg = true ->
  ~ (ly_reg L r <= z < ly_reg L r + rg_len rg) ->
  lsum (fun o => ind (inI (ly_reg L r + o) (ly_reg L r + o + PGSZ) z)) (rg_rw rg) = 0.
Proof. LiaFast.lf_pins (fun (HTOP FORB md HL : LiaFast.U) => LiaFast.u0).
  intros r rg z H1 Hk Hl Hz. apply lsum_zero. intros o Ho.
  assert (Hk' : rg_kind rg = RkMetaRes) by (unfold rk_meta in Hk; destruct (rg_kind rg); congruence).
  destruct (lk_rw _ _ _ _ _ HL r rg (conj H1 (conj Hk' Hl))) as (_ & AL). destruct (AL o Ho) as (A1 & A2 & A3).
  replace (inI (ly_reg L r + o) (ly_reg L r + o + PGSZ) z) with false by (symmetry; apply inI_false; unfold PGSZ in *; lia). reflexivity.
Qed.

#[using="HTOP FORB md HL"] Lemma region_term_le1 : forall r rg z, nth_error (kf_regions x) r = Some rg ->
  0 <= (if rk_meta rg && rg_live rg then lsum (fun o => ind (inI (ly_reg L r + o) (ly_reg L r + o + PGSZ) z)) (rg_rw rg) else 0) <= 1.
Proof. LiaFast.lf_pins (fun (HTOP FORB md HL : LiaFast.U) => LiaFast.u0).
  intros r rg z H1. destruct (rk_meta rg) eqn:Hk; destruct (rg_live rg) eqn:Hl; cbn [andb]; try lia.
  assert (Hk' : rg_kind rg = RkMetaRes) by (unfold rk_meta in Hk; destruct (rg_kind rg); congruence).
  destruct (lk_rw _ _ _ _ _ HL r rg (conj H1 (conj Hk' Hl))) as (ND & AL).
  split; [apply lsum_nonneg; intros o; apply ind_range|]. apply lsum_le1; [exact ND | intros o; apply ind_range|].
  intros o1 o2 I1 I2 Hne. destruct (AL o1 I1) as (A1 & _). destruct (AL o2 I2) as (A2 & _).
  destruct (inI (ly_reg L r + o1) (ly_reg L r + o1 + PGSZ) z) eqn:E1; [|left; reflexivity]. right.
  apply inI_true in E1. replace (inI (ly_reg L r + o2) (ly_reg L r + o2 + PGSZ) z) with false
    by (symmetry; apply inI_false; exact (pages_apart (ly_reg L r) o1 o2 z A1 A2 Hne E1)). reflexivity.
Qed.

#[using="HTOP FORB md HL"] Lemma OPF_le1 : forall z, OPF z <= 1.
Proof. LiaFast.lf_pins (fun (HTOP FORB md HL : LiaFast.U) => LiaFast.u0).
  intros z. unfold OPF. apply isum_le1.
  - intros r rg E. exact (region_term_le1 r rg z E).
  - intros r1 r2 rg1 rg2 Hne E1 E2. cbn [Nat.add].
    destruct (rk_meta rg1 && rg_live rg1) eqn:K1; [|left; reflexivity]. destruct (rk_meta rg2 && rg_live rg2) eqn:K2; [|right; reflexivity].
    apply andb_true_iff in K1 as [K1 L1]. apply andb_true_iff in K2 as [K2 L2].
    destruct (Z_le_dec (ly_reg L r1) z); [destruct (Z_lt_le_dec z (ly_reg L r1 + rg_len rg1))|].
    + destruct (Z_le_dec (ly_reg L r2) z); [destruct (Z_lt_le_dec z (ly_reg L r2 + rg_len rg2))|].
      * exfalso. apply Hne. exact (two_regions r1 r2 rg1 rg2 z E1 E2 L1 L2 ltac:(lia) ltac:(lia)).
      * right. apply (page_term_zero r2 rg2 z E2 K2 L2). lia.
      * right. apply (page_term_zero r2 rg2 z E2 K2 L2). lia.
    + left. apply (page_term_zero r1 rg1 z E1 K1 L1). lia.
    + left. apply (page_term_zero r1 rg1 z E1 K1 L1). lia.
Qed.

#[using="HTOP FORB HL"] Lemma OPF_na : forall z, inC (vm_noaccess (m_vmmaps md)) z = true -> OPF z = 0.
Proof. LiaFast.lf_pins (fun (HTOP FORB HL : LiaFast.U) => LiaFast.u0).
  intros z Hz. unfold OPF. apply isum_zero. intros r rg E. cbn [Nat.add].
  destruct (rk_meta rg && rg_live rg) eqn:K; [|reflexivity]. apply andb_true_iff in K as [Kk Kl].
  assert (Hk' : rg_kind rg = RkMetaRes) by (unfold rk_meta in Kk; destruct (rg_kind rg); congruence).
  destruct (lk_rw _ _ _ _ _ HL r rg (conj E (conj Hk' Kl))) as (_ & AL).
  apply lsum_zero. intros o Ho. destruct (AL o Ho) as (A1 & A2 & A3).
  destruct (inI (ly_reg L r + o) (ly_reg L r + o + PGSZ) z) eqn:Ep; [|reflexivity]. exfalso. apply inI_true in Ep.
  destruct (lk_na _ _ _ _ _ HL z Hz) as [((rb & rgb & B1 & B2 & B3 & B4) & Hg)|(rq & rgq & oq & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8)].
  - (* [comment removed for export] *)
    assert (Hne : rb <> r) by (intros ->; rewrite E in B1; injection B1 as <-; congruence).
    pose proof (rgeo_len rb rgb B1 B3) as Lb.
    pose proof (two_regions r rb rg rgb z E B1 Kl B3 ltac:(unfold PGSZ in *; lia) ltac:(rewrite B4; unfold PGSZ in *; lia)) as Er.
    congruence.
  - destruct (Nat.eq_dec rq r) as [->|Hne].
    + rewrite E in Q1. injection Q1 as <-.
      assert (Hoq : o <> oq) by (intros ->; exact (Q7 Ho)).
      exact (pages_apart (ly_reg L r) o oq z A1 Q6 Hoq Ep Q8).
    + pose proof (two_regions r rq rg rgq z E Q1 Kl Q3 ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ in *; lia)) as Er.
      congruence.
Qed.

#[using="HTOP FORB HL"] Lemma OPF_le_cut : forall z, OPF z <= cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1) z.
Proof. LiaFast.lf_pins (fun (HTOP FORB HL : LiaFast.U) => LiaFast.u0).
  intros z. rewrite cutall_spec. destruct (inC (vm_noaccess (m_vmmaps md)) z) eqn:E.
  - rewrite (OPF_na z E). lia.
  - exact (OPF_le1 z).
Qed.

#[using="HTOP FORB HL"] Lemma page_Wt : forall r rg o, nth_error (kf_regions x) r = Some rg -> rg_live rg = true ->
  0 <= o -> o + PGSZ <= rg_len rg -> o mod PGSZ = 0 ->
  PGSZ <= Wt (vm_maps (m_vmmaps md)) (fun z => ind (inI (ly_reg L r + o) (ly_reg L r + o + PGSZ) z)).
Proof. LiaFast.lf_pins (fun (HTOP FORB HL : LiaFast.U) => LiaFast.u0).
  intros r rg o H1 H2 H3 H4 H5. destruct (lk_rcov _ _ _ _ _ HL r rg o H1 H2 H3 H4 H5) as (e & He & (C1 & C2)).
  pose proof (Wt_cover (vm_maps (m_vmmaps md)) e (fun z => ind (inI (ly_reg L r + o) (ly_reg L r + o + PGSZ) z))
                (ly_reg L r + o) (ly_reg L r + o + PGSZ) He ltac:(intros z; apply ind_range) C1 ltac:(unfold PGSZ; lia) C2) as W.
  rewrite sumr_ind_full in W by (unfold PGSZ; lia). lia.
Qed.

#[using="HTOP FORB L HL"] Theorem opened_backed : PGSZ * ropen (kf_regions x) <= Wt (vm_maps (m_vmmaps md)) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1)).
Proof. LiaFast.lf_pins (fun (HTOP FORB L HL : LiaFast.U) => LiaFast.u0).
  eapply Z.le_trans; [|exact (Wt_mono _ _ _ OPF_le_cut)]. unfold OPF. rewrite Wt_isum.
  rewrite (ropen_isum (kf_regions x) 0).
  assert (T : forall rs k, (forall r rg, nth_error rs r = Some rg -> nth_error (kf_regions x) (k + r)%nat = Some rg) ->
     PGSZ * isum (fun _ rg => if rk_meta rg then Z.of_nat (length (rg_rw rg)) else 0) k rs <=
     isum (fun r rg => Wt (vm_maps (m_vmmaps md)) (fun z =>
              if rk_meta rg && rg_live rg then lsum (fun o => ind (inI (ly_reg L r + o) (ly_reg L r + o + PGSZ) z)) (rg_rw rg) else 0)) k rs).
  { induction rs as [|rg rs IH]; intros k Hrs; cbn [isum]; [lia|].
    pose proof (IH (S k) ltac:(intros r rg' E; rewrite Nat.add_succ_comm; exact (Hrs (S r) rg' E))) as IHk.
    pose proof (Hrs 0%nat rg eq_refl) as E0. rewrite Nat.add_0_r in E0.
    enough (PGSZ * (if rk_meta rg then Z.of_nat (length (rg_rw rg)) else 0) <=
            Wt (vm_maps (m_vmmaps md)) (fun z => if rk_meta rg && rg_live rg
                 then lsum (fun o => ind (inI (ly_reg L k + o) (ly_reg L k + o + PGSZ) z)) (rg_rw rg) else 0)) by lia.
    destruct (rk_meta rg) eqn:Kk; [|cbn [andb]; rewrite Wt_0; lia].
    assert (Hk' : rg_kind rg = RkMetaRes) by (unfold rk_meta in Kk; destruct (rg_kind rg); congruence).
    rewrite (lk_k0 _ _ _ _ _ HL k rg E0 Hk'). cbn [andb]. rewrite Wt_lsum.
    destruct (lk_rw _ _ _ _ _ HL k rg (conj E0 (conj Hk' (lk_k0 _ _ _ _ _ HL k rg E0 Hk')))) as (_ & AL).
    apply lsum_ge. intros o Ho. destruct (AL o Ho) as (A1 & A2 & A3).
    exact (page_Wt k rg o E0 (lk_k0 _ _ _ _ _ HL k rg E0 Hk') ltac:(unfold PGSZ in *; lia) A3 A1). }
  exact (T (kf_regions x) 0%nat ltac:(intros r rg E; exact E)).
Qed.

(* [comment removed for export] *)

Definition RSF (z : Z) : Z :=
  isum (fun r rg => if rk_meta rg && rg_live rg then ind (inI (ly_reg L r) (ly_reg L r + rg_len rg) z) else 0) 0 (kf_regions x).

#[using="HTOP FORB HL"] Lemma na_le : forall z, ind (inC (vm_noaccess (m_vmmaps md)) z) <= ind (inI (ly_brk0 L) (ly_brk0 L + PGSZ) z) + RSF z.
Proof. LiaFast.lf_pins (fun (HTOP FORB HL : LiaFast.U) => LiaFast.u0).
  intros z.
  assert (NN : forall r rg, 0 <= (if rk_meta rg && rg_live rg then ind (inI (ly_reg L r) (ly_reg L r + rg_len rg) z) else 0)).
  { intros r rg. destruct (rk_meta rg && rg_live rg); [pose proof (ind_range (inI (ly_reg L r) (ly_reg L r + rg_len rg) z)); lia | lia]. }
  assert (RS0 : 0 <= RSF z) by (apply isum_nonneg; exact NN).
  pose proof (ind_range (inI (ly_brk0 L) (ly_brk0 L + PGSZ) z)).
  destruct (inC (vm_noaccess (m_vmmaps md)) z) eqn:E; cbn [ind]; [|lia].
  destruct (lk_na _ _ _ _ _ HL z E) as [(_ & Hg)|(rq & rgq & oq & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8)].
  - replace (inI (ly_brk0 L) (ly_brk0 L + PGSZ) z) with true by (symmetry; apply inI_true; exact Hg). cbn [ind]. lia.
  - assert (T1 : (if rk_meta rgq && rg_live rgq then ind (inI (ly_reg L rq) (ly_reg L rq + rg_len rgq) z) else 0) = 1).
    { unfold rk_meta. rewrite Q2, Q3. cbn [andb].
      replace (inI (ly_reg L rq) (ly_reg L rq + rg_len rgq) z) with true by (symmetry; apply inI_true; unfold PGSZ in *; lia). reflexivity. }
    pose proof (isum_term (fun r rg => if rk_meta rg && rg_live rg then ind (inI (ly_reg L r) (ly_reg L r + rg_len rg) z) else 0)
                  (kf_regions x) 0 rq rgq NN Q1) as T.
    cbn [Nat.add] in T. rewrite T1 in T. unfold RSF. lia.
Qed.

#[using="HTOP FORB L HL"] Theorem na_bound : Wt (vm_maps (m_vmmaps md)) (fun z => ind (inC (vm_noaccess (m_vmmaps md)) z)) <= PGSZ + rtot (kf_regions x).
Proof. LiaFast.lf_pins (fun (HTOP FORB L HL : LiaFast.U) => LiaFast.u0).
  eapply Z.le_trans; [exact (Wt_mono _ _ _ na_le)|]. rewrite Wt_add.
  assert (G : Wt (vm_maps (m_vmmaps md)) (fun z => ind (inI (ly_brk0 L) (ly_brk0 L + PGSZ) z)) <= PGSZ).
  { pose proof (Wt_disj_le (vm_maps (m_vmmaps md)) (fun z => ind (inI (ly_brk0 L) (ly_brk0 L + PGSZ) z)) (ly_brk0 L) (ly_brk0 L + PGSZ)
                  (lk_mdisj _ _ _ _ _ HL) ltac:(unfold PGSZ; lia) ltac:(intros z; apply ind_range)
                  ltac:(intros z Hz; cbv beta; replace (inI (ly_brk0 L) (ly_brk0 L + PGSZ) z) with false by (symmetry; apply inI_false; lia); reflexivity)) as W.
    rewrite sumr_ind_full in W by (unfold PGSZ; lia). lia. }
  assert (R : Wt (vm_maps (m_vmmaps md)) RSF <= rtot (kf_regions x)).
  { unfold RSF. rewrite Wt_isum. rewrite (rtot_isum (kf_regions x) 0). apply isum_mono'. intros r rg E. cbn [Nat.add].
    destruct (rk_meta rg) eqn:Kk; destruct (rg_live rg) eqn:Kl; cbn [andb]; rewrite ?Wt_0.
    - pose proof (rgeo_len r rg E Kl) as Hp.
      pose proof (Wt_disj_le (vm_maps (m_vmmaps md)) (fun z => ind (inI (ly_reg L r) (ly_reg L r + rg_len rg) z)) (ly_reg L r) (ly_reg L r + rg_len rg)
                    (lk_mdisj _ _ _ _ _ HL) ltac:(unfold PGSZ in *; lia) ltac:(intros z; apply ind_range)
                    ltac:(intros z Hz; cbv beta; replace (inI (ly_reg L r) (ly_reg L r + rg_len rg) z) with false by (symmetry; apply inI_false; lia); reflexivity)) as W.
      rewrite sumr_ind_full in W by (unfold PGSZ in *; lia). lia.
    - assert (Hk' : rg_kind rg = RkMetaRes) by (unfold rk_meta in Kk; destruct (rg_kind rg); congruence).
      rewrite (lk_k0 _ _ _ _ _ HL r rg E Hk') in Kl. discriminate Kl.
    - lia.
    - lia. }
  lia.
Qed.

#[using="HTOP FORB L HL"] Theorem ledger_bound : ledger_size (vm_maps (m_vmmaps md)) <=
  Wt (vm_maps (m_vmmaps md)) (cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1)) + PGSZ + rtot (kf_regions x).
Proof. LiaFast.lf_pins (fun (HTOP FORB L HL : LiaFast.U) => LiaFast.u0).
  assert (E : ledger_size (vm_maps (m_vmmaps md)) = Wt (vm_maps (m_vmmaps md)) (fun _ => 1)).
  { rewrite <- live_bytes_Wt. clear. induction (vm_maps (m_vmmaps md)) as [|[a s] l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. }
  rewrite E. rewrite (Wt_ext _ (fun _ => 1) (fun z => cutall (vm_noaccess (m_vmmaps md)) (fun _ => 1) z + ind (inC (vm_noaccess (m_vmmaps md)) z)))
    by (intros p z _ _; rewrite cutall_spec; destruct (inC (vm_noaccess (m_vmmaps md)) z); reflexivity).
  rewrite Wt_add. pose proof na_bound. lia.
Qed.

End Meas.
