(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Junk.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L L' : list (Z * Z)) (M : mem).
  Variables (p n m i off res : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st m.
  Hypothesis Hi : 0 <= i <= g_lastidx st m.
  Hypothesis Hslot : s_slot st m i = SUser p n off res.
  Hypothesis HL'in : forall x, In x L' <-> In x L /\ x <> (p, n).
  Hypothesis HL'nd : NoDup L'.
  Hypothesis HL'len : (length L' <= length L)%nat.

  Definition st' : mst := set_slot st m i (SJunk off).

  Lemma e_slot : forall x k, s_slot st' x k = if (Z.eqb x m && Z.eqb k i)%bool then SJunk off else s_slot st x k.
  Proof. intros. reflexivity. Qed.
  Lemma e_slot_mi : s_slot st' m i = SJunk off.
  Proof. rewrite e_slot, !Z.eqb_refl. reflexivity. Qed.
  Lemma e_slot_other : forall x k, (x <> m \/ k <> i) -> s_slot st' x k = s_slot st x k.
  Proof. intros x k H. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn; try reflexivity. exfalso; lia. Qed.

  Lemma e_glast : forall x, g_lastidx st' x = g_lastidx st x. Proof. reflexivity. Qed.
  Lemma e_gsc : forall x, g_sc st' x = g_sc st x. Proof. reflexivity. Qed.
  Lemma e_gml : forall x, g_maplen st' x = g_maplen st x. Proof. reflexivity. Qed.
  Lemma e_gss : forall x k, g_slot_start st' x k = g_slot_start st x k. Proof. reflexivity. Qed.
  Lemma e_gse : forall x k, g_slot_end st' x k = g_slot_end st x k. Proof. reflexivity. Qed.
  Lemma e_gstride : forall x, g_stride st' x = g_stride st x. Proof. reflexivity. Qed.
  Lemma e_gmem : forall x, g_mem st' x = g_mem st x. Proof. reflexivity. Qed.


  Lemma t_wfg : wf_group st L m. Proof. exact (U_wfg st L HWF m Hgrp). Qed.
  Lemma t_pure : 0 <= off /\ 0 <= n /\ p = g_slot_start st m i + 16 * off /\ res = g_stride st m - IB - n - 16 * off /\
                 0 <= res < 2 ^ 31 /\ ptr_ok st m i p /\ In (p, n) L.
  Proof. exact (U_pure st L HWF p n m i off res Hgrp Hi Hslot). Qed.
  Lemma t_same_ptr : forall x k n2 o2 r2, is_group st x -> 0 <= k <= g_lastidx st x ->
    s_slot st x k = SUser p n2 o2 r2 -> x = m /\ k = i.
  Proof.
    intros x k n2 o2 r2 Hx Hk Hs.
    exact (wL_fun st L (WF_live st L HWF) x k m i p n2 n o2 off r2 res Hx Hgrp Hk Hi Hs Hslot).
  Qed.

  (* [comment removed for export] *)
  Lemma e_slot_ptr : forall x k, slot_ptr st' x k = slot_ptr st x k.
  Proof.
    intros x k. unfold slot_ptr. change (g_slot_start st' x k) with (g_slot_start st x k). rewrite e_slot.
    destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb]; try reflexivity.
    subst. rewrite Hslot. destruct t_pure as (_ & _ & Hp & _). rewrite Hp. reflexivity.
  Qed.

  Lemma t_gcell_back : forall x a, gcell st' x a -> gcell st x a.
  Proof.
    intros x a G. unfold gcell in *.
    change (g_mem st' x) with (g_mem st x) in G. change (g_cnt st' x) with (g_cnt st x) in G.
    change (g_lastidx st' x) with (g_lastidx st x) in G.
    destruct G as [G | [G | [G | G]]].
    - left. exact G.
    - right. left. exact G.
    - right. right. left. destruct G as (k & q & Hk & Hp & Ha). exists k, q. rewrite e_slot_ptr in Hp. tauto.
    - right. right. right. destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & Ha). exists k, q, n2, o2, r2.
      change (g_slot_end st' x k) with (g_slot_end st x k) in Ha. split; [exact Hk|]. split; [|exact Ha].
      rewrite e_slot in Hs. destruct (Z.eqb x m && Z.eqb k i)%bool; [discriminate Hs | exact Hs].
  Qed.


  Lemma t_appb_back : forall a, appb st' a -> appb st a.
  Proof.
    intros a (x & k & q & n2 & o2 & r2 & Hx & Hk & Hs & Ha).
    change (g_lastidx st' x) with (g_lastidx st x) in Hk. change (is_group st x) in Hx.
    rewrite e_slot in Hs. destruct (Z.eqb x m && Z.eqb k i)%bool; [discriminate Hs|].
    exists x, k, q, n2, o2, r2. repeat split; try assumption; lia.
  Qed.

  Lemma t_garbage_back : forall x k a, garbage st' x k a ->
    garbage st x k a \/ (x = m /\ k = i /\ (g_slot_start st m i - 3 <= a < p - 4 \/ p <= a < g_slot_end st m i)).
  Proof.
    intros x k a [Hk G]. unfold garbage.
    change (g_lastidx st' x) with (g_lastidx st x) in Hk.
    change (g_slot_start st' x k) with (g_slot_start st x k) in G. change (g_slot_end st' x k) with (g_slot_end st x k) in G.
    rewrite e_slot in G.
    destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb] in G.
    - right. subst. destruct t_pure as (_ & _ & Hp & _). rewrite Hp in *. repeat split; try lia.
    - left. split; [exact Hk|]. destruct (s_slot st x k); try exact G.
    - left. split; [exact Hk|]. destruct (s_slot st x k); try exact G.
    - left. split; [exact Hk|]. destruct (s_slot st x k); try exact G.
  Qed.

  (* [comment removed for export] *)
  Lemma t_old_range : forall a, p <= a < g_slot_end st m i ->
    appb st a \/ gcell st m a \/ garbage st m i a.
  Proof.
    intros a Ha. destruct t_pure as (Hoff & Hn & Hp & Hres & Hr & PO & HinL).
    assert (He : g_slot_end st m i = p + n + res) by (unfold g_slot_end, IB in *; lia).
    destruct (Z.lt_ge_cases a (p + n)) as [C|C].
    { left. exists m, i, p, n, off, res. repeat split; try assumption; lia. }
    destruct (Z.eq_dec a (p + n)) as [->|D].
    { right. left. unfold gcell. right. right. right. exists i, p, n, off, res. split; [exact Hi|]. split; [exact Hslot|]. left. lia. }
    destruct (Z.lt_ge_cases a (g_slot_end st m i - 5)) as [E|E].
    { right. right. unfold garbage. rewrite Hslot. split; [exact Hi|]. right. left. lia. }
    destruct (Z.lt_ge_cases res 5) as [F|F].
    { right. right. unfold garbage. rewrite Hslot. split; [exact Hi|]. right. right. lia. }
    right. left. unfold gcell. right. right. right. exists i, p, n, off, res. split; [exact Hi|]. split; [exact Hslot|]. right. lia.
  Qed.

  Lemma t_slot_wf : forall x k sl, is_group st x -> 0 <= k <= g_lastidx st x -> (x <> m \/ k <> i) ->
    s_slot st x k = sl -> slot_wf st L x k sl -> slot_wf st' L' x k sl.
  Proof.
    intros x k sl Hx Hk Hne Hs SW. destruct sl as [| |q n2 o2 r2|c o2|o2]; cbn [slot_wf] in *; try exact I; try exact SW.
    destruct SW as (A & B & C & D & E & F & G). conjs; try assumption; try lia.
    apply HL'in. split; [exact G|]. intros Heq. assert (Eq : q = p) by congruence.
    rewrite Eq in Hs. destruct (t_same_ptr x k n2 o2 r2 Hx Hk Hs) as [-> ->]. destruct Hne; congruence.
  Qed.

  Lemma t_wf_group : forall x, is_group st x -> wf_group st' L' x.
  Proof.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; try assumption.
    - intros k Hk. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb]; try exact (Av k Hk).
      subst. rewrite (Av i ltac:(lia)), Hslot. split; intros [A B]; split; try assumption; discriminate B.
    - intros k Hk. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb]; try exact (Fr k Hk).
      subst. rewrite (Fr i ltac:(lia)), Hslot. split; intros [A B]; split; try assumption; discriminate B.
    - intros k Hk. rewrite e_slot. destruct (Z.eqb x m && Z.eqb k i)%bool; [intros E; discriminate E | exact (Avai k Hk)].
    - intros k Hk. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb]; try exact (High k Hk).
      subst. pose proof (High i Hk) as E. rewrite Hslot in E. discriminate E.
    - intros Hall. apply Full. intros k Hk. specialize (Hall k Hk). rewrite e_slot in Hall.
      destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb] in Hall; try exact Hall.
      subst. rewrite Hslot. split; intros E; discriminate E.
    - change (s_kind st' x) with (s_kind st x). destruct (s_kind st x) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride, ?e_gml. conjs; try assumption; try lia. rewrite e_slot_other; [exact K6|].
      destruct (Z.eq_dec hm m) as [->|]; [right | left; assumption]. intros ->. rewrite Hslot in K6. discriminate K6.
    - intros Hall. apply FF. intros k Hk. specialize (Hall k Hk). rewrite e_slot in Hall.
      destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb] in Hall; try exact Hall.
      destruct Hall as [E|E]; discriminate E.
    - intros k Hk. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb].
      + subst. cbn [slot_wf]. destruct t_pure as (Hoff & Hn & Hp & Hres & Hr & PO & HinL).
        split; [exact Hoff|]. split; [rewrite e_gstride; unfold IB in *; lia|]. rewrite e_gss, <- Hp. exact PO.
      + apply t_slot_wf; [exact Hx | exact Hk | right; assumption | reflexivity | exact (Slots k Hk)].
      + apply t_slot_wf; [exact Hx | exact Hk | left; assumption | reflexivity | exact (Slots k Hk)].
      + apply t_slot_wf; [exact Hx | exact Hk | left; assumption | reflexivity | exact (Slots k Hk)].
    - intros Hsc Hst k Hk. rewrite e_slot. destruct (Z.eqb x m && Z.eqb k i)%bool; [split; intros E; discriminate E | exact (Fit Hsc Hst k Hk)].
  Qed.

  Lemma t_wf_geom : wf_geom st'.
  Proof.
    destruct (WF_geom st L HWF) as [INR CELLS AREA APC APA APD GC GA GAR SPAN].
    constructor; try assumption.
    - intros m1 m2 a H1 H2 Hne G1 G2. exact (CELLS m1 m2 a H1 H2 Hne (t_gcell_back m1 a G1) (t_gcell_back m2 a G2)).
    - intros x a Hx G Ap. exact (APC x a Hx (t_gcell_back x a G) (t_appb_back a Ap)).
    - intros a Ap Ar. exact (APA a (t_appb_back a Ap) Ar).
    - intros m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne.
      change (g_lastidx st' m1) with (g_lastidx st m1) in Hk1. change (g_lastidx st' m2) with (g_lastidx st m2) in Hk2.
      rewrite e_slot in S1, S2.
      destruct (Z.eqb m1 m && Z.eqb k1 i)%bool; [discriminate S1|]. destruct (Z.eqb m2 m && Z.eqb k2 i)%bool; [discriminate S2|].
      exact (APD m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne).
    - intros x k a x2 Hx G H2 C. pose proof (t_gcell_back x2 a C) as C'.
      destruct (t_garbage_back x k a G) as [G' | (-> & -> & Ha)]; [exact (GC x k a x2 Hx G' H2 C')|].
      destruct t_pure as (Hoff & Hn & Hp & Hres & Hr & PO & HinL).
      destruct Ha as [Ha|Ha].
      + apply (GC m i a x2 Hgrp); [|exact H2|exact C']. unfold garbage. rewrite Hslot. split; [exact Hi|]. left. exact Ha.
      + destruct (t_old_range a Ha) as [Ap | [Cm | Gb]].
        * exact (APC x2 a H2 C' Ap).
        * destruct (Z.eq_dec x2 m) as [->|Hx2].
          -- (* [comment removed for export] *)
             pose proof (wg_stride st L m t_wfg) as [S16 _].
             assert (He : g_slot_end st m i = p + n + res) by (unfold g_slot_end, IB in *; lia).
             unfold gcell in C.
             change (g_mem st' m) with (g_mem st m) in C. change (g_cnt st' m) with (g_cnt st m) in C. change (g_lastidx st' m) with (g_lastidx st m) in C.
             pose proof (wg_mem st L m t_wfg) as (M1 & M2 & M3).
             destruct C as [C | [C | [C | C]]].
             ++ unfold g_slot_start, UNIT in Hp. assert (0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; lia). lia.
             ++ destruct C as (k & Hk & Hak & _). change (g_slot_start st' m k) with (g_slot_start st m k) in Hak.
                unfold g_slot_end, g_slot_start, UNIT, IB in *.
                assert (g_stride st m * i < g_stride st m * k) by lia.
                assert (g_stride st m * k < g_stride st m * (i + 1)) by lia.
                assert (i < k) by (apply (Z.mul_lt_mono_pos_l (g_stride st m)); lia).
                assert (k < i + 1) by (apply (Z.mul_lt_mono_pos_l (g_stride st m)); lia). lia.
             ++ destruct C as (k & q & Hk & Hq & Hak). rewrite e_slot_ptr in Hq.
                pose proof (gcell_in_span st L HWF m a Hgrp) as _.
                destruct (Z.eq_dec k i) as [->|Hki].
                { unfold slot_ptr in Hq. rewrite Hslot in Hq. injection Hq. intros <-. lia. }
                (* [comment removed for export] *)
                pose proof (wg_slots st L m t_wfg k Hk) as SW. unfold slot_ptr in Hq.
                assert (R : g_slot_start st m k - 4 <= a < g_slot_end st m k).
                { destruct (s_slot st m k) as [| |q2 n2 o2 r2|c o2|o2] eqn:Es; try discriminate Hq; injection Hq; intros <-; cbn [slot_wf] in SW.
                  - destruct SW as (A & B & C0 & D & E & _). unfold g_slot_end, IB in *. lia.
                  - destruct SW as (A & B & C0 & D & E).
                    pose proof (wg_kind st L c (wG_each st L (WF_groups st L HWF) c B)) as KC. rewrite D in KC.
                    destruct KC as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
                    pose proof (wg_stride st L c (wG_each st L (WF_groups st L HWF) c B)) as [SC _].
                    assert (0 <= g_lastidx st c) by (unfold g_lastidx, w_lastidx; apply Z.mod_pos_bound; lia).
                    assert (0 <= g_cnt st c * g_stride st c) by (apply Z.mul_nonneg_nonneg; unfold g_cnt; lia).
                    unfold g_slot_end, UNIT, IB in *. lia.
                  - destruct SW as (A & B & C0). unfold g_slot_end, IB in *. lia. }
                destruct (Z.lt_ge_cases k i) as [Hl|Hg].
                { assert (g_stride st m * (k + 1) <= g_stride st m * i) by (apply Z.mul_le_mono_nonneg_l; lia).
                  unfold g_slot_end, g_slot_start, UNIT, IB in *. lia. }
                { assert (g_stride st m * (i + 1) <= g_stride st m * k) by (apply Z.mul_le_mono_nonneg_l; lia).
                  unfold g_slot_end, g_slot_start, UNIT, IB in *. lia. }
             ++ destruct C as (k & q & n2 & o2 & r2 & Hk & Hs & Hak). change (g_slot_end st' m k) with (g_slot_end st m k) in Hak.
                rewrite e_slot in Hs. rewrite Z.eqb_refl in Hs. cbn [andb] in Hs.
                destruct (Z.eqb_spec k i) as [->|Hki]; [discriminate Hs|].
                pose proof (wg_slots st L m t_wfg k Hk) as SW. rewrite Hs in SW. cbn [slot_wf] in SW.
                destruct SW as (A & B & C0 & D & E & _).
                destruct (Z.lt_ge_cases k i) as [Hl|Hg].
                { assert (g_stride st m * (k + 1) <= g_stride st m * i) by (apply Z.mul_le_mono_nonneg_l; lia).
                  unfold g_slot_end, g_slot_start, UNIT, IB in *. lia. }
                { assert (g_stride st m * (i + 1) <= g_stride st m * k) by (apply Z.mul_le_mono_nonneg_l; lia).
                  unfold g_slot_end, g_slot_start, UNIT, IB in *. lia. }
          -- exact (CELLS m x2 a Hgrp H2 ltac:(congruence) Cm C').
        * exact (GC m i a x2 Hgrp Gb H2 C').
    - intros x k a Hx G Ap. pose proof (t_appb_back a Ap) as Ap'.
      destruct (t_garbage_back x k a G) as [G' | (-> & -> & Ha)]; [exact (GA x k a Hx G' Ap')|].
      destruct Ha as [Ha|Ha].
      + apply (GA m i a Hgrp); [|exact Ap']. unfold garbage. rewrite Hslot. split; [exact Hi|]. left. exact Ha.
      + pose proof Ap' as (x2 & k2 & q2 & n2 & o2 & r2 & H2 & Hk2 & Hs2 & Ha2).
        pose proof Ap as (x3 & k3 & q3 & n3 & o3 & r3 & H3 & Hk3 & Hs3 & Ha3).
        change (g_lastidx st' x3) with (g_lastidx st x3) in Hk3. change (is_group st x3) in H3.
        rewrite e_slot in Hs3.
        assert (N3 : x3 <> m \/ k3 <> i).
        { destruct (Z.eqb_spec x3 m); destruct (Z.eqb_spec k3 i); cbn [andb] in Hs3; try discriminate Hs3;
            first [right; assumption | left; assumption]. }
        destruct (Z.eqb_spec x3 m); destruct (Z.eqb_spec k3 i); cbn [andb] in Hs3; try discriminate Hs3.
        all: destruct (t_old_range a Ha) as [Ap0 | [Cm | Gb]]; [| exact (APC m a Hgrp Cm Ap') | exact (GA m i a Hgrp Gb Ap')].
        all: destruct t_pure as (Hoff & Hn & Hp & Hres & Hr & PO & HinL).
        all: destruct (Z.lt_ge_cases a (p + n)) as [Hin|Hout];
          [ destruct (APD x3 k3 m i q3 n3 o3 r3 p n off res H3 Hgrp Hk3 Hi Hs3 Hslot ltac:(intros E; injection E; intros; subst; destruct N3; congruence)); lia
          | ].
        all: destruct (t_old_range a Ha) as [_ | [Cm | Gb]]; [| exact (APC m a Hgrp Cm Ap') | exact (GA m i a Hgrp Gb Ap')].
        all: assert (He : g_slot_end st m i = p + n + res) by (unfold g_slot_end, IB in *; lia).
        all: (* [comment removed for export] *)
             destruct (Z.eq_dec a (p + n)) as [->|D];
             [ apply (APC m (p + n) Hgrp); [|exact Ap']; unfold gcell; right; right; right; exists i, p, n, off, res;
               split; [exact Hi|]; split; [exact Hslot|]; left; lia | ].
        all: destruct (Z.lt_ge_cases a (g_slot_end st m i - 5)) as [E5|E5];
             [ apply (GA m i a Hgrp); [|exact Ap']; unfold garbage; rewrite Hslot; split; [exact Hi|]; right; left; lia | ].
        all: destruct (Z.lt_ge_cases res 5) as [F5|F5];
             [ apply (GA m i a Hgrp); [|exact Ap']; unfold garbage; rewrite Hslot; split; [exact Hi|]; right; right; lia | ].
        all: apply (APC m a Hgrp); [|exact Ap']; unfold gcell; right; right; right; exists i, p, n, off, res;
             split; [exact Hi|]; split; [exact Hslot|]; right; lia.
    - intros x k a Hx G Ar.
      destruct (t_garbage_back x k a G) as [G' | (-> & -> & Ha)]; [exact (GAR x k a Hx G' Ar)|].
      apply (AREA m a Hgrp); [|exact Ar].
      destruct t_pure as (Hoff & Hn & Hp & Hres & Hr & PO & HinL).
      pose proof (wg_stride st L m t_wfg) as [S16 _]. pose proof (wg_mem st L m t_wfg) as (M1 & _).
      unfold gspan, g_span_end, g_slot_end, g_slot_start, UNIT, IB in *.
      assert (0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; lia).
      assert (g_stride st m * (i + 1) <= g_stride st m * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
      lia.
  Qed.

  Lemma t_wf_live : wf_live st' L'.
  Proof.
    destruct (WF_live st L HWF) as [IN ND FUN LEN].
    constructor.
    - intros q n2 Hin. apply HL'in in Hin. destruct Hin as [Hin Hne].
      destruct (IN q n2 Hin) as (x & k & o2 & r2 & Hx & Hk & Hs).
      exists x, k, o2, r2. split; [exact Hx|]. split; [exact Hk|]. rewrite e_slot_other; [exact Hs|].
      destruct (Z.eq_dec x m) as [->|]; [right|left; assumption]. intros ->. rewrite Hslot in Hs. injection Hs. intros; subst. apply Hne. reflexivity.
    - exact HL'nd.
    - intros m1 i1 m2 i2 q n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2.
      change (g_lastidx st' m1) with (g_lastidx st m1) in Hk1. change (g_lastidx st' m2) with (g_lastidx st m2) in Hk2.
      rewrite e_slot in S1, S2.
      destruct (Z.eqb m1 m && Z.eqb i1 i)%bool; [discriminate S1|]. destruct (Z.eqb m2 m && Z.eqb i2 i)%bool; [discriminate S2|].
      exact (FUN m1 i1 m2 i2 q n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2).
    - pose proof LEN. lia.
  Qed.

  Lemma t_wf_regions : wf_regions st'.
  Proof.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; try assumption.
    intros b len x Hin Hx63.
    destruct (G63 b len x Hin Hx63) as [(q & n2 & o2 & r2 & Hs & Hlen) | (o2 & Hs)].
    - rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec 0 i); cbn [andb].
      + right. exists off. reflexivity.
      + left. exists q, n2, o2, r2. split; assumption.
      + left. exists q, n2, o2, r2. split; assumption.
      + left. exists q, n2, o2, r2. split; assumption.
    - right. rewrite e_slot. destruct (Z.eqb x m && Z.eqb 0 i)%bool; [exists off; reflexivity | exists o2; exact Hs].
  Qed.

  Lemma t_wf_img : wf_img st'.
  Proof. apply (wf_img_same st L HWF); reflexivity. Qed.

  Lemma t_WF : WF st' L'.
  Proof.
    destruct HWF as (C & A & Ls & G & Ge & Lv & R).
    split; [destruct C; constructor; assumption|]. split; [destruct A; constructor; assumption|].
    split; [destruct Ls; constructor; assumption|]. split.
    - destruct G as [ND EACH ONE REG FR0 OTH LIM ONEFF]. constructor; try assumption.
      + intros x Hx. apply t_wf_group. exact Hx.
      + intros m1 m2 H1 H2 F1 F2 E. apply (ONEFF m1 m2 H1 H2); [intros k Hk | intros k Hk | exact E].
        * specialize (F1 k Hk). rewrite e_slot in F1. destruct (Z.eqb m1 m && Z.eqb k i)%bool; [destruct F1 as [F|F]; discriminate F | exact F1].
        * specialize (F2 k Hk). rewrite e_slot in F2. destruct (Z.eqb m2 m && Z.eqb k i)%bool; [destruct F2 as [F|F]; discriminate F | exact F2].
    - split; [exact t_wf_geom|]. split; [exact t_wf_live |]. split; [exact t_wf_regions | exact t_wf_img].
  Qed.

  Lemma rep_slot_conv : forall x k sl, rep_slot st M x k sl -> rep_slot st' M x k sl.
  Proof.
    intros x k sl RS. destruct sl; cbn [rep_slot] in *; try exact I.
    - destruct RS as (RH & A & B). split; [destruct RH; constructor; assumption | split; assumption].
    - destruct RS as (rc & Hrc & RH). exists rc. split; [exact Hrc | destruct RH; constructor; assumption].
  Qed.

  Lemma t_REP : REP st' M.
  Proof.
    destruct HREP as [ST CX AR GR]. constructor.
    { destruct ST; constructor; assumption. }
    { destruct CX; constructor; assumption. }
    { intros ar Har. destruct (AR ar Har); constructor; assumption. }
    intros x Hx. pose proof (GR x Hx) as [Hm Hai Hh Hd Hs].
    constructor; try assumption.
    intros k Hk. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb]; try (apply rep_slot_conv; exact (Hs k Hk)).
    subst. cbn [rep_slot]. exact I.
  Qed.

  Theorem junk_close : WF st' L' /\ REP st' M.
  Proof. split; [exact t_WF | exact t_REP]. Qed.
End Junk.
