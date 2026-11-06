(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLin AxVal AxBytes AxMem AxZZ AxState AxSys.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section WithSegs.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.

(* [comment removed for export] *)
Definition same_part (w z : Z) : Prop :=
  (ls_beg <= w < ls_end /\ ls_beg <= z < ls_end) \/ (hs_beg <= w < hs_hi /\ hs_beg <= z < hs_hi).

(* [comment removed for export] *)
Lemma ss_mapped (ρ : valuation) (A : list region) (m : word -> option byte) (W : region) (w z : Z) :
  RMem segs ρ A m -> hs_ok ρ A m -> In W A -> is_shadow W = true -> in_rg ρ W w -> same_part w z -> m (wz z) <> None.
Proof.
  intros [Hok HR] Hhs0 HW Hs Hw Hpart. destruct (hs_old_of_sh ρ A m W HW Hs Hhs0) as [_ [_ [P3 P4]]].
  pose proof (regions_ok_in ρ A W Hok HW) as Hwf. pose proof (proj1 (Forall_forall _ _) HR W HW) as HRW.
  apply (RRegion_sh segs ρ m W Hs) in HRW. unfold in_rg in Hw.
  pose proof (smod_range ρ (rg_ts W) (rg_bo W)) as Hb. fold (rbase ρ W) in Hb.
  assert (Hx : to_Z (of_Z (w - rbase ρ W)) = w - rbase ρ W).
  { rewrite of_Z_spec. apply Z.mod_small. destruct Hwf as (_ & H47 & _). change wB with (2 ^ 63). lia. }
  destruct (HRW (of_Z (w - rbase ρ W)) ltac:(lia)) as [_ Hwv]. rewrite Hx in Hwv.
  replace (rbase ρ W + (w - rbase ρ W)) with w in Hwv by lia.
  specialize (Hwv ltac:(unfold is_shadow in Hs; destruct (rg_kind W); first [reflexivity | discriminate Hs])).
  assert (Hss : in_ss w) by (unfold in_ss; destruct Hpart as [[X _]|[X _]]; [left | right]; exact X).
  assert (Hmw : m (wz w) <> None).
  { apply (wview_mapped segs m w Hlow Hss); [|exact Hwv]. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, two64 in *. lia. }
  destruct Hpart as [[Hp Hq]|[Hp Hq]].
  - destruct P3 as [X|X]; [exact (X z Hq) | exfalso; exact (Hmw (X w Hp))].
  - destruct P4 as [X|X]; [exact (X z Hq) | exfalso; exact (Hmw (X w Hp))].
Qed.

Section PostFix.
Variable ρ : valuation.
Variable A : list region.
Variables m m' : word -> option byte.
Variables model model' : Model.
Variables a n : Z.
Variables R0 C0 : region.

Hypothesis HR0k : rg_kind R0 = KZero.
Hypothesis HR0c : rg_cells R0 = IEmpty.
Hypothesis HR0b : rbase ρ R0 = a.
Hypothesis HR0n : to_Z (rg_n R0) = n.
Hypothesis HR0wf : region_wf ρ R0.
Hypothesis HC0k : rg_kind C0 = KShadow.
Hypothesis HC0c : rg_cells C0 = IEmpty.
Hypothesis HC0b : rbase ρ C0 = a / 8 + sh_off.
Hypothesis HC0n : to_Z (rg_n C0) = n / 8.
Hypothesis HC0wf : region_wf ρ C0.
Hypothesis Ha8 : a mod 8 = 0.
Hypothesis Hn8 : n mod 8 = 0.
Hypothesis Ha0 : 0 <= a.
Hypothesis Hn0 : 0 < n.

Hypothesis Hm_in : forall z, a <= z < a + n -> m' (wz z) = Some (Z_to_bv 8 0).
Hypothesis Hm_out : forall x : word, ~ (a <= bv_unsigned x < a + n) -> m' x = m x.

Hypothesis HRM : RMem segs ρ A m.
Hypothesis Hhs : hs_ok ρ A m.
Hypothesis Hcomp : comp_inv segs ρ A model.
Hypothesis Hcov : mem_cov segs model m.
Hypothesis Hna : na_ok segs ρ A model m.

Hypothesis HA_fresh : forall R, In R A -> is_shadow R = false -> forall z, in_rg ρ R z -> ~ (a <= z < a + n).
Hypothesis HA_C_disj : forall R, In R A -> is_shadow R = true -> forall z, in_rg ρ R z -> ~ in_rg ρ C0 z.
Hypothesis Hside : a + n <= sh_lo \/ sh_hi <= a.
Hypothesis Htop : a + n <= 2 ^ 47.
(* [comment removed for export] *)
Hypothesis Hled_new_w : forall q, a <= q < a + n -> in_ledger_w segs (m_vmmaps model') q.
Hypothesis Hled_old_w : forall q, in_ledger_w segs (m_vmmaps model) q -> in_ledger_w segs (m_vmmaps model') q.
Lemma Hled_new : forall q, a <= q < a + n -> in_ledger segs (m_vmmaps model') q.
Proof. intros q Hq. exact (in_ledger_w_in segs _ q (Hled_new_w q Hq)). Qed.
Lemma Hled_old : forall q, in_ledger segs (m_vmmaps model) q -> in_ledger segs (m_vmmaps model') q.
Proof. exact (in_ledger_of_w segs _ _ Hled_old_w). Qed.
Hypothesis Hna_new : forall q, a <= q < a + n -> ~ inl (vm_noaccess (m_vmmaps model')) q.
Hypothesis Hna_old : forall q, inl (vm_noaccess (m_vmmaps model')) q -> inl (vm_noaccess (m_vmmaps model)) q.
Hypothesis HC_mapped : forall z, in_rg ρ C0 z -> m (wz z) <> None.
Hypothesis HA_pos : forall R, In R A -> 0 < to_Z (rg_n R).

(* [comment removed for export] *)
Let Hold : hs_old ρ A m := hs_old_of_pos ρ A m HA_pos Hhs.

(* [comment removed for export] *)
Lemma fix_not_ss (z : Z) : a <= z < a + n -> ~ in_ss z.
Proof. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, sh_lo, sh_hi in *. lia. Qed.

(* [comment removed for export] *)
Lemma C0_in_ss (z : Z) : in_rg ρ C0 z -> in_ss z.
Proof.
  unfold in_rg. rewrite HC0b, HC0n. intros Hz.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. rewrite Ha8 in Da. rewrite Hn8 in Dn.
  unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, sh_lo, sh_hi, sh_off in *. lia.
Qed.

Lemma C0_preimage (z q : Z) : in_rg ρ C0 z -> preimage z q -> a <= q < a + n.
Proof.
  unfold in_rg, preimage. rewrite HC0b, HC0n. intros Hz Hq.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. rewrite Ha8 in Da. rewrite Hn8 in Dn. lia.
Qed.

Lemma mem_same_ss (z : Z) : in_ss z -> m' (wz z) = m (wz z).
Proof.
  intros Hz. apply Hm_out. rewrite u_wz by (unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in Hz; lia).
  intros Hr. exact (fix_not_ss z Hr Hz).
Qed.

(* [comment removed for export] *)
Lemma old_frame (R : region) : In R A -> forall z, in_rg ρ R z -> m' (wz z) = m (wz z).
Proof.
  intros HR z Hz. destruct HRM as [Hok _]. pose proof (regions_ok_in ρ A R Hok HR) as (Hw1 & _).
  pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hb. fold (rbase ρ R) in Hb. unfold in_rg in Hz.
  apply Hm_out. rewrite u_wz by (unfold two64 in *; lia). destruct (is_shadow R) eqn:Es.
  - intros Hr. exact (fix_not_ss z Hr (proj1 (Hcomp R HR Es z Hz))).
  - exact (HA_fresh R HR Es z Hz).
Qed.

Lemma rdisj_R0_C0 : rdisj ρ R0 C0.
Proof.
  unfold rdisj. rewrite HR0b, HR0n, HC0b, HC0n.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. rewrite Ha8 in Da. rewrite Hn8 in Dn.
  unfold sh_lo, sh_hi, sh_off in *. lia.
Qed.

Lemma rdisj_R0_old (R : region) : In R A -> rdisj ρ R0 R.
Proof.
  intros HR. unfold rdisj. rewrite HR0b, HR0n. destruct HRM as [Hok _]. pose proof (regions_ok_in ρ A R Hok HR) as (Hw1 & _).
  pose proof (HA_pos R HR) as Hz.
  destruct (Z_le_gt_dec (a + n) (rbase ρ R)) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (rbase ρ R + to_Z (rg_n R)) a) as [L2|L2]; [right; exact L2|]. exfalso.
  set (z := Z.max a (rbase ρ R)). assert (Hzr : in_rg ρ R z) by (unfold in_rg, z; lia).
  assert (Hza : a <= z < a + n) by (unfold z; lia).
  destruct (is_shadow R) eqn:Es.
  - exact (fix_not_ss z Hza (proj1 (Hcomp R HR Es z Hzr))).
  - exact (HA_fresh R HR Es z Hzr Hza).
Qed.

Lemma rdisj_C0_old (R : region) : In R A -> rdisj ρ C0 R.
Proof.
  intros HR. unfold rdisj. destruct HRM as [Hok _]. pose proof (regions_ok_in ρ A R Hok HR) as (Hw1 & _).
  destruct (Z_le_gt_dec (rbase ρ C0 + to_Z (rg_n C0)) (rbase ρ R)) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (rbase ρ R + to_Z (rg_n R)) (rbase ρ C0)) as [L2|L2]; [right; exact L2|]. exfalso.
  pose proof (HA_pos R HR) as Hz.
  destruct (Z_le_gt_dec (to_Z (rg_n C0)) 0) as [Hz0|Hz0]; [lia|].
  set (z := Z.max (rbase ρ C0) (rbase ρ R)). assert (Hzr : in_rg ρ R z) by (unfold in_rg, z; lia).
  assert (Hzc : in_rg ρ C0 z) by (unfold in_rg, z; lia).
  destruct (is_shadow R) eqn:Es.
  - exact (HA_C_disj R HR Es z Hzr Hzc).
  - destruct Hold as [P1 _]. exact (P1 R HR Es z Hzr (C0_in_ss z Hzc)).
Qed.

Lemma RRegion_R0 : RRegion segs ρ m' R0.
Proof.
  rewrite RRegion_ne by (unfold is_entry; rewrite HR0k; reflexivity). intros y Hy.
  pose proof (to_Z_bounded y) as Hyb. rewrite HR0b. rewrite HR0n in Hy.
  assert (E : m' (wz (a + to_Z y)) = Some (Z_to_bv 8 0)) by (apply Hm_in; lia). split.
  - exists (Z_to_bv 8 0). split; [unfold rv; rewrite E; reflexivity|].
    rewrite (rbyte_zz segs R0 y (or_introl HR0k) HR0c). reflexivity.
  - intros _. unfold wview. rewrite E. discriminate.
Qed.

Lemma RRegion_C0 : RRegion segs ρ m' C0.
Proof.
  rewrite RRegion_ne by (unfold is_entry; rewrite HC0k; reflexivity). intros y Hy.
  pose proof (to_Z_bounded y) as Hyb.
  assert (Hin : in_rg ρ C0 (rbase ρ C0 + to_Z y)) by (unfold in_rg; lia).
  pose proof (C0_in_ss _ Hin) as Hss.
  pose proof (HC_mapped _ Hin) as Hmp. destruct Hold as [_ [P2 _]].
  destruct (P2 _ Hss (fun R HR Hs Hr => HA_C_disj R HR Hs _ Hr Hin)) as [E|E]; [contradiction|].
  rewrite <- (mem_same_ss _ Hss) in E. split.
  - exists (Z_to_bv 8 0). split; [unfold rv; rewrite E; reflexivity|].
    rewrite (rbyte_zz segs C0 y (or_intror HC0k) HC0c). reflexivity.
  - intros _. unfold wview. rewrite E. discriminate.
Qed.

Theorem RMem_fix : RMem segs ρ (R0 :: C0 :: A) m'.
Proof.
  destruct HRM as [Hok HR]. split.
  - cbn [regions_ok]. split; [exact HR0wf|]. split.
    + constructor; [exact rdisj_R0_C0|]. apply Forall_forall. exact rdisj_R0_old.
    + split; [exact HC0wf|]. split; [apply Forall_forall; exact rdisj_C0_old | exact Hok].
  - constructor; [exact RRegion_R0|]. constructor; [exact RRegion_C0|].
    apply Forall_forall. intros R HRin. apply (RRegion_mframe segs ρ m m' R (regions_ok_in ρ A R Hok HRin)).
    + intros z Hz. exact (old_frame R HRin z Hz).
    + exact (proj1 (Forall_forall _ _) HR R HRin).
Qed.

Theorem hs_ok_fix : hs_ok ρ (R0 :: C0 :: A) m'.
Proof.
  destruct Hold as [P1 [P2 [P3 P4]]]. right. split; [|split; [|split]].
  - intros R [<-|[<-|HR]] Hs z Hz.
    + unfold in_rg in Hz. rewrite HR0b, HR0n in Hz. exact (fix_not_ss z Hz).
    + unfold is_shadow in Hs. rewrite HC0k in Hs. discriminate Hs.
    + exact (P1 R HR Hs z Hz).
  - intros z Hss Hout. rewrite (mem_same_ss z Hss). apply (P2 z Hss). intros R HR Hs. exact (Hout R (or_intror (or_intror HR)) Hs).
  - destruct P3 as [X|X]; [left | right]; intros z Hz; rewrite (mem_same_ss z (or_introl Hz)); exact (X z Hz).
  - destruct P4 as [X|X]; [left | right]; intros z Hz; rewrite (mem_same_ss z (or_intror Hz)); exact (X z Hz).
Qed.

Theorem comp_inv_fix : comp_inv segs ρ (R0 :: C0 :: A) model'.
Proof.
  intros R [<-|[<-|HR]] Hs z Hz.
  - unfold is_shadow in Hs. rewrite HR0k in Hs. discriminate Hs.
  - split; [exact (C0_in_ss z Hz)|]. intros q Hq. exact (Hled_new q (C0_preimage z q Hz Hq)).
  - destruct (Hcomp R HR Hs z Hz) as [H1 H2]. split; [exact H1|]. intros q Hq. exact (Hled_old q (H2 q Hq)).
Qed.

Theorem mem_cov_fix : mem_cov segs model' m'.
Proof.
  intros x Hx. destruct (Z_le_gt_dec a (bv_unsigned x)) as [L1|L1]; [destruct (Z_lt_le_dec (bv_unsigned x) (a + n)) as [L2|L2]|].
  - apply Hled_new_w. lia.
  - rewrite Hm_out in Hx by lia. exact (Hled_old_w _ (Hcov x Hx)).
  - rewrite Hm_out in Hx by lia. exact (Hled_old_w _ (Hcov x Hx)).
Qed.

Theorem na_ok_fix : na_ok segs ρ (R0 :: C0 :: A) model' m'.
Proof.
  destruct Hna as [N1 [N2 N3]]. split; [|split].
  - intros x Hx Hi. destruct (Z_le_gt_dec a (bv_unsigned x)) as [L1|L1]; [destruct (Z_lt_le_dec (bv_unsigned x) (a + n)) as [L2|L2]|].
    + exact (Hna_new (bv_unsigned x) (conj L1 L2) Hi).
    + rewrite Hm_out in Hx by lia. exact (N1 x Hx (Hna_old _ Hi)).
    + rewrite Hm_out in Hx by lia. exact (N1 x Hx (Hna_old _ Hi)).
  - intros z Hz Hi. exact (N2 z Hz (Hna_old _ Hi)).
  - intros R [<-|[<-|HR]] Hs z Hz q Hq Hi.
    + unfold is_shadow in Hs. rewrite HR0k in Hs. discriminate Hs.
    + exact (Hna_new q (C0_preimage z q Hz Hq) Hi).
    + exact (N3 R HR Hs z Hz q Hq (Hna_old _ Hi)).
Qed.

End PostFix.

End WithSegs.
