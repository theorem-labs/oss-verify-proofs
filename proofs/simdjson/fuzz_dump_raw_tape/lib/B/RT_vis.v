(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import MState Mem Frame Cells ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require BackingAlgebra.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs RT_state RT_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma shreg_off : forall a : word, shreg (bv_unsigned a) -> find_segment bsegs (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply (find_segment1_none_above bsegs SEGTOP_A _ asegs_below).
  unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *. lia.
Qed.

Lemma wview_shreg : forall (m : mem) (a : word), shreg (bv_unsigned a) -> wview bsegs m a = m a.
Proof. intros m a H. unfold wview. destruct (m a); [reflexivity|]. rewrite (shreg_off a H). reflexivity. Qed.

Lemma vis_rep_agree : forall L A (m m' : mem), vis_rep L A m ->
  (forall a : word, shreg (bv_unsigned a) -> m a <> None -> m' a <> None) -> vis_rep L A m'.
Proof. intros L A m m' H Hs a Ha Hp Hlo Hx. exact (Hs a Ha (H a Ha Hp Hlo Hx)). Qed.

Lemma vis_rep_mono_A : forall L A A' (m : mem), vis_rep L A m ->
  (forall p, page_allowedb A' p = true -> page_allowedb A p = true) -> vis_rep L A' m.
Proof. intros L A A' m H Hs a Ha Hp Hlo Hx. exact (H a Ha (Hs _ Hp) Hlo Hx). Qed.

Lemma vis_rep_nret : forall L A (ms : machine_state) (eff : SyscallEffect),
  eff_copies eff = [] -> eff_writes eff = [] ->
  (forall a : word, shreg (bv_unsigned a) -> zeros_cover (eff_unmaps eff) a = false) ->
  vis_rep L A (ms_mem ms) -> vis_rep L A (ms_mem (nretA ms eff)).
Proof.
  intros L A ms eff Hc Hw Hu H. apply (vis_rep_agree L A _ _ H). intros a Ha Hn. specialize (Hu a Ha).
  unfold nretA, advance_past_svc, apply_effect. cbn [ms_mem]. rewrite Hc, Hw. cbn [apply_copies apply_writes].
  unfold set_reg. cbn [ms_mem].
  assert (U : apply_unmaps (ms_mem ms) (eff_unmaps eff) a = ms_mem ms a).
  { unfold apply_unmaps. destruct (eff_unmaps eff); [reflexivity|]. rewrite Hu. reflexivity. }
  unfold apply_zeros. destruct (eff_zeros eff) as [|z zs]; [rewrite U; exact Hn|].
  destruct (zeros_cover (z :: zs) a); [discriminate|]. rewrite U. exact Hn.
Qed.

Lemma page_base_lt' : forall a : word, bv_unsigned a < bv_unsigned (page_base a) + 4096.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R.
  pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)).
  rewrite unsigned_lit by (split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia | lia]). lia.
Qed.

Lemma ast_allow_x : forall segs segtop A X Pm PM,
  A_wf X ->
  (forall mo, PM mo -> (eager_used mo + A_bytes X + A_bytes A <= vm_limit (m_vmmaps mo))%Z) ->
  cps segs (AST segtop A Pm PM)
    (AST segtop (X ++ A) (fun ms => exists ms0 mo, PM mo /\ Pm ms0 /\ revealed A (X ++ A) mo ms0 ms
                                     /\ (forall a, HID A mo a = true -> ms_mem ms0 a = None /\ segtop <= bv_unsigned a)
                                     /\ (forall a, HID (X ++ A) mo a = true -> ms_mem ms a = None)) PM).
Proof.
  intros segs segtop A X Pm PM HX Hb T [ms mo] (Hmc & HPm & HPMmo & HZ0) Hk. cbn [cfg_ms cfg_model] in *. apply Hk.
  pose proof Hmc as (HAwf & [M1 M2 M3 M4 M5] & Hh & Hr & Ht).
  assert (HA' : A_wf (X ++ A)) by (apply A_wf_app; assumption).
  assert (Hsub : forall p, page_allowedb A p = true -> page_allowedb (X ++ A) p = true) by (apply page_allowedb_app_l).
  split.
  { split; [exact HA'|]. split; [|split; [assumption| split; assumption]].
    constructor; [exact M1| exact M2| intros p Hp; apply Hsub; exact (M3 p Hp)| exact M4|].
    rewrite A_bytes_app. specialize (Hb mo HPMmo). cbn [cfg_model]. lia. }
  cbn [cfg_ms cfg_model]. split; [|split; [exact HPMmo|]].
  - exists (restrict (HID A mo) ms), mo. split; [exact HPMmo|]. split; [exact HPm|]. split; [split; [reflexivity|]; split|].
    + intros a Ha. cbn. unfold mrestrict. rewrite Ha.
      destruct (HID (X ++ A) mo a) eqn:E; [|reflexivity]. rewrite (HID_mono A (X ++ A) mo a Hsub E) in Ha. discriminate.
    + intros a Ha Ha' Hna. cbn. unfold mrestrict. rewrite Ha'. exact (HZ0 a (mkH_of_HID A (X ++ A) mo a Ha Ha') Hna).
    + split.
      * intros a Ha. cbn. unfold mrestrict. rewrite Ha. split; [reflexivity|].
        unfold HID in Ha. apply orb_true_iff in Ha as [Ha|Ha]; [exact (mkH_above _ A segtop a Hr Ha)| apply Z.leb_le in Ha; lia].
      * intros a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity.
  - intros a Ha Hna. exact (HZ0 a (mkH_mono _ A (X ++ A) a Hsub Ha) Hna).
Qed.

Section Reveal.
Variables (A X : list (Z * Z)) (mo : Model) (ms0 ms : machine_state).
Hypothesis HR : revealed A (X ++ A) mo ms0 ms.
Hypothesis HH0 : forall a, HID A mo a = true -> ms_mem ms0 a = None /\ SEGTOP_A <= bv_unsigned a.
Hypothesis HH1 : forall a, HID (X ++ A) mo a = true -> ms_mem ms a = None.

Lemma reveal_wmono : wmono bsegs (ms_mem ms0) (ms_mem ms).
Proof using HR HH0.
  intros a Hw. destruct HR as (_ & Hv & _). destruct (HID A mo a) eqn:E.
  - exfalso. destruct (HH0 a E) as (N & Ht). apply Hw. unfold wview. rewrite N.
    rewrite (find_segment1_none_above bsegs SEGTOP_A _ asegs_below Ht). reflexivity.
  - unfold wview in *. rewrite (Hv a E). exact Hw.
Qed.

Lemma reveal_munch : forall W, (forall a : word, page_allowedb X (page_base a) = true -> page_allowedb A (page_base a) = false ->
    ~ outside W (bv_unsigned a)) -> munch W (ms_mem ms0) (ms_mem ms).
Proof using HR HH0 HH1.
  intros W HW x Hx. destruct HR as (_ & Hv & _). destruct (HID A mo x) eqn:E1; [|exact (Hv x E1)].
  destruct (HID (X ++ A) mo x) eqn:E2; [rewrite (HH1 x E2); exact (eq_sym (proj1 (HH0 x E1)))|].
  exfalso. unfold HID, mkH in E1, E2. apply orb_false_iff in E2 as [E2 E3]. rewrite E3, orb_false_r in E1.
  apply andb_prop in E1 as [L1 N1]. rewrite L1 in E2. cbn [andb] in E2. apply negb_true_iff in N1. apply negb_false_iff in E2.
  unfold page_allowedb in E2. rewrite existsb_app in E2. fold (page_allowedb X (page_base x)) in E2.
  fold (page_allowedb A (page_base x)) in E2. rewrite N1, orb_false_r in E2. exact (HW x E2 N1 Hx).
Qed.

Lemma vis_rep_reveal : forall L, shadow_lazy mo -> vis_rep L A (ms_mem ms0) -> vis_rep L (X ++ A) (ms_mem ms).
Proof using HR.
  intros L0 HL H a Ha Hp Hlo Hx. destruct HR as (_ & Hv & Hz).
  pose proof (HL a Ha) as (Hlz & Hna).
  assert (Hlt : bv_unsigned a < 2 ^ 47) by (unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in *; lia).
  destruct (page_allowedb A (page_base a)) eqn:EA.
  - rewrite Hv; [exact (H a Ha EA Hlo Hx)|]. unfold HID, mkH. rewrite Hlz, EA. cbn. apply Z.leb_gt. exact Hlt.
  - rewrite Hz; [discriminate| | |].
    + unfold HID, mkH. rewrite Hlz, EA. reflexivity.
    + unfold HID, mkH. rewrite Hlz, Hp. cbn. apply Z.leb_gt. exact Hlt.
    + destruct (page_in_ranges (page_base a) (vm_noaccess (m_vmmaps mo))) eqn:E; [|reflexivity]. exfalso.
      unfold page_in_ranges in E. apply existsb_exists in E as (r & Hr & Hrr). apply andb_prop in Hrr as [R1 R2].
      apply Z.leb_le in R1. apply Z.leb_le in R2.
      pose proof (page_base_le a). pose proof (page_base_lt' a). unfold page_size in R2.
      assert (C : BackingAlgebra.covered (vm_noaccess (m_vmmaps mo)) (bv_unsigned a) = true).
      { unfold BackingAlgebra.covered. apply existsb_exists. exists r. split; [exact Hr|].
        unfold BackingAlgebra.in_iv, BackingAlgebra.in_rng, BackingAlgebra.B, BackingAlgebra.S.
        apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      rewrite C in Hna. discriminate.
Qed.
End Reveal.

End GWIN.
