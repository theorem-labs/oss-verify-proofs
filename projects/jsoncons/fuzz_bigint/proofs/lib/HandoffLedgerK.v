(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec AgentLib AsanAcct BackingAlgebra AsanPlacement AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK HandoffBridgeK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hl_covered_in_ivs : forall l z, BackingAlgebra.covered l z = in_ivs z l.
Proof. intros l z. unfold BackingAlgebra.covered, in_ivs. induction l as [|q l IH]; [reflexivity|]. cbn [existsb]. rewrite IH. reflexivity. Qed.

Lemma hl_seps_apart : forall l, seps l ->
  forall q q', In q l -> In q' l -> q <> q' ->
    BackingAlgebra.B q + BackingAlgebra.S q <= BackingAlgebra.B q' \/ BackingAlgebra.B q' + BackingAlgebra.S q' <= BackingAlgebra.B q.
Proof.
  intros l Hs. induction Hs as [|p l Hp Hs IH]; intros q q' Hq Hq' Hne; [destruct Hq|].
  unfold BackingAlgebra.B, BackingAlgebra.S in *.
  destruct Hq as [<-|Hq]; destruct Hq' as [<-|Hq'].
  - congruence.
  - exact (proj1 (Forall_forall _ _) Hp q' Hq').
  - pose proof (proj1 (Forall_forall _ _) Hp q Hq) as D. unfold iv_disjoint in D. lia.
  - exact (IH q q' Hq Hq' Hne).
Qed.

Lemma hl_seps_nodup : forall l, seps l -> (forall q, In q l -> 0 < bv_unsigned (snd q)) -> List.NoDup l.
Proof.
  intros l Hs. induction Hs as [|p l Hp Hs IH]; intros Hpos; [constructor|].
  constructor.
  - intros Hin. pose proof (proj1 (Forall_forall _ _) Hp p Hin) as D. unfold iv_disjoint in D.
    pose proof (Hpos p (or_introl eq_refl)). lia.
  - apply IH. intros q Hq. apply Hpos. right. exact Hq.
Qed.

(* [comment removed for export] *)
Lemma hl_iv_subtract : forall (a sz : word) lo hi q,
  bv_unsigned a + bv_unsigned sz <= 2 ^ 64 -> 0 < bv_unsigned sz ->
  In q (iv_subtract a sz lo hi) ->
  0 < bv_unsigned (snd q) /\ bv_unsigned a <= bv_unsigned (fst q)
  /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a + bv_unsigned sz.
Proof.
  intros a sz lo hi q Hwf Hpos Hin. unfold iv_subtract in Hin.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma hl_maps_subtract : forall l lo hi q,
  (forall p, In p l -> bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64 /\ 0 < bv_unsigned (snd p)) ->
  In q (maps_subtract l lo hi) ->
  0 < bv_unsigned (snd q)
  /\ exists p, In p l /\ bv_unsigned (fst p) <= bv_unsigned (fst q)
               /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p) + bv_unsigned (snd p).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hl Hin; [destruct Hin|].
  cbn [maps_subtract] in Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (Hl (a, sz) (or_introl eq_refl)) as [W P]. cbn [fst snd] in W, P.
    destruct (hl_iv_subtract a sz lo hi q W P Hin) as (Q1 & Q2 & Q3).
    split; [exact Q1|]. exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. lia.
  - destruct (IH lo hi q (fun p Hp => Hl p (or_intror Hp)) Hin) as (Q1 & p & Hp & Q2 & Q3).
    split; [exact Q1|]. exists p. split; [right; exact Hp|]. lia.
Qed.

(* [comment removed for export] *)
Lemma hl_replay : forall E h,
  (forall b n, In (HCons b n) h -> uE E b + uE E n <= 2 ^ 64 /\ 0 < uE E n) ->
  forall q, In q (hreplay E h) ->
    0 < bv_unsigned (snd q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64
    /\ exists b n, In (HCons b n) h /\ uE E b <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= uE E b + uE E n.
Proof.
  intros E h. induction h as [|hop h IH]; intros Hh q Hin; [destruct Hin|].
  destruct hop as [b n|b n]; cbn [hreplay] in Hin.
  - destruct Hin as [<-|Hin].
    + destruct (Hh b n (or_introl eq_refl)) as [W P]. cbn [fst snd]. unfold uE in *.
      split; [exact P|]. split; [exact W|]. exists b, n. split; [left; reflexivity|]. lia.
    + destruct (IH (fun b' n' H' => Hh b' n' (or_intror H')) q Hin) as (Q1 & Q2 & b' & n' & Hb & Q3 & Q4).
      split; [exact Q1|]. split; [exact Q2|]. exists b', n'. split; [right; exact Hb|]. lia.
  - assert (IH' := IH (fun b' n' H' => Hh b' n' (or_intror H'))).
    destruct (hl_maps_subtract (hreplay E h) _ _ q (fun p Hp => let '(conj P1 (conj P2 _)) := IH' p Hp in conj P2 P1) Hin) as (Q1 & p & Hp & Q2 & Q3).
    destruct (IH' p Hp) as (P1 & P2 & b' & n' & Hb & P3 & P4).
    split; [exact Q1|]. split; [lia|]. exists b', n'. split; [right; exact Hb|]. lia.
Qed.

(* [comment removed for export] *)
Lemma hl_in_amapb : forall m ms, existsb (amap_eqb m) ms = true -> In m ms.
Proof. intros m ms H. apply existsb_exists in H as (m' & Hin & Heq). apply amap_eqb_eq in Heq. subst m'. exact Hin. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition len_within (n len : expr) : bool :=
  (expr_eqb len n || match n, len with ELit z, ELit L => (Z.ltb 0 z && Z.leb z L && Z.ltb L (2 ^ 64))%bool | _, _ => false end)%bool.
Definition hop_in_maps (ms : list amap) (hp : hop) : bool :=
  match hp with
  | HCons b n => existsb (fun m => negb (is_fog m) && expr_eqb (am_base m) b && len_within n (am_len m))%bool ms   (* [comment removed for export] *)
  | HSub _ _ => true
  end.
Definition hops_in_maps (ms : list amap) (h : list hop) : bool := forallb (hop_in_maps ms) h.

Section Ledger.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (hid A argH).
(* [comment removed for export] *)
Let HSd : nat -> option acs := fun _ => None.
Let XNd : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XEd : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XBd : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
#[local] Notation PIRI := (page_in_ranges_In HSd XNd XEd XBd 0%nat).
#[local] Notation PBLE := (page_base_le HSd XNd XEd XBd 0%nat).

Lemma hl_alloc_top : forall E cs R FULL model, CSOK E cs R FULL model ->
  alloc_top (m_vmmaps model) = uE E e_sp0 - 8388608.
Proof.
  intros E cs R FULL model HC. destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (H1 & _). unfold alloc_top, stack_max_size. rewrite H1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hl_maps_pos : forall E cs R FULL model q, CSOK E cs R FULL model -> In q (vm_maps (m_vmmaps model)) ->
  0 < bv_unsigned (snd q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= uE E e_sp0 - 8388608.
Proof.
  intros E cs R FULL model q HC Hin.
  pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) q Hin) as (P1 & _ & _ & _ & P5).
  pose proof (utop_bounds E). split; [exact P1 | lia].
Qed.

(* [comment removed for export] *)
Lemma hl_hop_in_maps : forall E cs R FULL model h, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) h = true ->
  forall b n, In (HCons b n) h ->
    exists q, In q (vm_maps (m_vmmaps model)) /\ fst q = edenot E b /\ 0 < uE E n <= bv_unsigned (snd q).
Proof.
  intros E cs R FULL model h HC Hnf Hh b n Hin.
  pose proof (proj1 (forallb_forall _ _) Hh _ Hin) as Hb. cbn [hop_in_maps] in Hb.
  apply existsb_exists in Hb as (m & Hm & Hb). apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [_ Hb].
  apply expr_eqb_eq in Hb. subst b.
  assert (Hq : In (amap_den E m) (vm_maps (m_vmmaps model))).
  { rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). apply in_map_iff. exists m. split; [reflexivity | exact Hm]. }
  exists (amap_den E m). split; [exact Hq|]. split; [reflexivity|].
  pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hq) as (P1 & _).
  unfold amap_den in *. cbn [fst snd] in *. unfold len_within in Hn. apply orb_prop in Hn as [Hn|Hn].
  - apply expr_eqb_eq in Hn. rewrite <- Hn. unfold uE. lia.
  - destruct n as [z|n0|o a1 a2|o a1 a2|o a1 a2|o a1 a2|sx lo0 n0 e0|sx k0 i0 n0]; try discriminate.
    destruct (am_len m) as [L|n1|o b1 b2|o b1 b2|o b1 b2|o b1 b2|sx lo1 n1 e1|sx k1 i1 n1]; try discriminate.
    apply andb_prop in Hn as [Hn H3]. apply andb_prop in Hn as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    unfold uE. cbn [edenot]. rewrite !u64_lit by lia. lia.
Qed.

Lemma hl_hops_ok : forall E cs R FULL model h, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) h = true ->
  forall b n, In (HCons b n) h -> uE E b + uE E n <= 2 ^ 64 /\ 0 < uE E n.
Proof.
  intros E cs R FULL model h HC Hnf Hh b n Hin.
  destruct (hl_hop_in_maps E cs R FULL model h HC Hnf Hh b n Hin) as (q & Hq & Hb & Hn).
  destruct (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W & _).
  pose proof (W _ Hq) as Wq. unfold BackingAlgebra.iv_wf, BackingAlgebra.B, BackingAlgebra.S in Wq. rewrite Hb in Wq. unfold uE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma hl_noacc_pos : forall E cs R FULL model, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) (a_hna cs) = true ->
  forall q, In q (vm_noaccess (m_vmmaps model)) -> 0 < bv_unsigned (snd q).
Proof.
  intros E cs R FULL model HC Hnf Hh q Hin. rewrite (co_hna _ _ _ _ _ _ _ _ _ _ _ HC) in Hin.
  exact (proj1 (hl_replay E (a_hna cs) (hl_hops_ok E cs R FULL model _ HC Hnf Hh) q Hin)).
Qed.

(* [comment removed for export] *)
Lemma hl_lazy_in : forall E cs R FULL model, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) (a_hlz cs) = true ->
  forall a : word, page_in_ranges (page_base a) (m_vm_lazy model) = true ->
    in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true /\ find_segment SEGS (bv_unsigned a) 1 = None.
Proof.
  intros E cs R FULL model HC Hnf Hh a Hp.
  destruct (PIRI a _ Hp) as (iv & Hiv & B1 & B2 & _ & _).
  split.
  - rewrite (co_hlz _ _ _ _ _ _ _ _ _ _ _ HC) in Hiv.
    destruct (hl_replay E (a_hlz cs) (hl_hops_ok E cs R FULL model _ HC Hnf Hh) iv Hiv) as (_ & _ & b & n & Hb & Q1 & Q2).
    destruct (hl_hop_in_maps E cs R FULL model _ HC Hnf Hh b n Hb) as (q & Hq & Hqb & Hqn).
    unfold in_ivs. apply existsb_exists. exists q. split; [exact Hq|]. rewrite Hqb. unfold uE in *.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - apply SEGS_in_hull.
    pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) iv Hiv) as [L1 _].
    unfold in_hull. destruct L1 as [L1|L1]; apply andb_false_iff; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
Lemma hl_hidden_zero : forall E cs R FULL model, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) (a_hlz cs) = true ->
  forall a : word, mkH (m_vm_lazy model) (allowA A E cs) a = true ->
    in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
    FULL a = Some (Z_to_bv 8 0).
Proof.
  intros E cs R FULL model HC Hnf Hh a Hm Hna. unfold mkH in Hm. apply andb_prop in Hm as [Hlz Hal]. apply negb_true_iff in Hal.
  destruct (hl_lazy_in E cs R FULL model HC Hnf Hh a Hlz) as [Hin _].
  (* [comment removed for export] *)
  assert (Hhid : HID E cs model a = true).
  { destruct (HID E cs model a) eqn:Hh'; [reflexivity|]. exfalso.
    pose proof (lazy_cover_cs SEGS A LIMIT HSd XNd XEd XBd HULL_ok SINV argH FS0 0%nat E cs R FULL model HC a Hlz Hh') as Hc. congruence. }
  apply (hb_zero SEGS A LIMIT SINV argH FS0 E cs R FULL model a HC Hhid Hin Hna Hlz).
  (* [comment removed for export] *)
  destruct (in_ghost E cs (bv_unsigned a)) eqn:Hg; [exfalso | reflexivity].
  unfold in_ghost in Hg. apply existsb_exists in Hg as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
  apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
  assert (Hc : page_allowedb (allowA A E cs) (page_base a) = true); [|congruence].
  pose proof (PBLE a) as (P1 & P2 & P3).
  unfold page_allowedb, allowA. apply existsb_exists.
  exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
  - apply in_flat_map. exists p. split; [apply in_or_app; right; exact Hp|]. left. reflexivity.
  - cbn [fst snd]. unfold page_size.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHB_LO : Z := 0x7fff7000.
Definition SHB_LEN : Z := 0x100000001000.

(* [comment removed for export] *)
Definition vis_sh_wr (k : list kentry) (p : expr * expr) : bool :=
  let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in
  (Z.leb 3 (ealign k (fst p)) && flat_x k sb sk sn && existsb (kentry_eqb (KWr (SA sb sk) sn)) k)%bool.
Definition vis_off_band (k : list kentry) (p : expr * expr) : bool :=
  let '(bb, bk) := split_lit (fst p) in
  (flat_x k bb bk (snd p) && ranges_apart_x k (ELit SHB_LO) 0 (ELit SHB_LEN) bb bk (snd p))%bool.

Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis HULL_below : img_hi A <= SHB_LO.

Lemma hl_off_band : forall E cs R FULL model p z, CSOK E cs R FULL model -> vis_off_band (kn cs) p = true ->
  uE E (fst p) <= z < uE E (fst p) + uE E (snd p) -> ~ (SHB_LO <= z < SHB_LO + SHB_LEN).
Proof.
  intros E cs R FULL model p z HC Hv Hz Hband. unfold vis_off_band in Hv.
  destruct (split_lit (fst p)) as [bb bk] eqn:Hsp. apply andb_prop in Hv as [Hf Hap].
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) bb bk (snd p) HK Hf) as (F1 & F2 & F3).
  pose proof (split_lit_denot E _ bb bk Hsp) as Hd.
  assert (Hb : uE E (fst p) = estart E (SA bb bk)).
  { unfold uE. rewrite Hd. unfold estart in *; cbn [a_base a_off] in *. pose proof (u64_range (edenot E (snd p))). rewrite u64_lit by lia. reflexivity. }
  pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap) as D.
  unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
  unfold SHB_LO, SHB_LEN in *. rewrite !u64_lit in D by lia. unfold uE in *. lia.
Qed.

Lemma hl_shadow_defined : forall E cs R FULL model, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  forallb (vis_sh_wr (kn cs)) (a_vis cs) = true ->
  forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true ->
  forall m BL LL, In m (a_maps cs) -> am_kind m = KRWLAZY -> am_base m = ELit BL -> am_len m = ELit LL ->
    SHB_LO <= BL -> 0 <= LL -> BL + LL <= SHB_LO + SHB_LEN ->
  forall a : word, BL <= bv_unsigned a < BL + LL -> FULL a <> None.
Proof.
  intros E cs R FULL model HC Hnf Hwr Hoff m BL LL Hm Hk Hbase Hlen HB HL HBL a Ha.
  unfold SHB_LO, SHB_LEN in *.
  assert (Hden : bv_unsigned (edenot E (am_base m)) = BL /\ bv_unsigned (edenot E (am_len m)) = LL).
  { rewrite Hbase, Hlen. cbn [edenot]. rewrite !u64_lit by lia. auto. }
  destruct Hden as [D1 D2].
  destruct (hb_lazykind SEGS A LIMIT SINV argH FS0 E cs R FULL model m a HC Hm Hk ltac:(rewrite D1, D2; exact Ha)) as [Hna Hlz].
  assert (Hin : in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
  { rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). unfold in_ivs. apply existsb_exists.
    exists (amap_den E m). split; [apply in_map; exact Hm|]. unfold amap_den. cbn [fst snd]. rewrite D1, D2.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  pose proof (proj1 (forallb_forall _ _) Hoff) as Hoff'.
  destruct (HID E cs model a) eqn:Hh.
  - (* [comment removed for export] *)
    assert (Hg : in_ghost E cs (bv_unsigned a) = false).
    { destruct (in_ghost E cs (bv_unsigned a)) eqn:Hg; [exfalso | reflexivity].
      unfold in_ghost in Hg. apply existsb_exists in Hg as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      apply (hl_off_band E cs R FULL model p (bv_unsigned a) HC (Hoff' p (in_or_app _ _ _ (or_intror Hp))) (conj Hb1 Hb2)).
      unfold SHB_LO, SHB_LEN. lia. }
    rewrite (hb_zero SEGS A LIMIT SINV argH FS0 E cs R FULL model a HC Hh Hin Hna Hlz Hg). discriminate.
  - (* [comment removed for export] *)
    rewrite hb_hid_unfold in Hh. apply orb_false_iff in Hh as [_ Hv]. apply negb_false_iff in Hv. unfold vis in Hv.
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
    destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & (SPlo & _) & _).
    pose proof (utop_bounds E) as UT. unfold sp_window_lo in SPlo.
    apply orb_prop in Hv as [Hv|Hv].
    { exfalso. apply orb_prop in Hv as [Hv|Hv].
      - unfold in_hull in Hv. apply andb_prop in Hv as [_ Hv]. apply Z.ltb_lt in Hv. lia.
      - apply Z.leb_le in Hv. lia. }
    apply andb_prop in Hv as [_ Hv]. rewrite Hlz in Hv. cbn [negb orb] in Hv. unfold in_allow in Hv.
    apply orb_prop in Hv as [Hv|Hv].
    { exfalso. unfold in_vis in Hv. apply existsb_exists in Hv as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      apply (hl_off_band E cs R FULL model p (bv_unsigned a) HC (Hoff' p (in_or_app _ _ _ (or_introl Hp))) (conj Hb1 Hb2)).
      unfold SHB_LO, SHB_LEN. lia. }
    unfold in_sh in Hv. apply existsb_exists in Hv as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
    pose proof (proj1 (forallb_forall _ _) Hwr p Hp) as Hw. unfold vis_sh_wr in Hw.
    destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn] eqn:Hso.
    apply andb_prop in Hw as [Hw Hkw]. apply andb_prop in Hw as [Hal Hfl]. apply Z.leb_le in Hal.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (shadow_of_val SEGS A SHADOW_ok E _ (kn cs) (fst p) (snd p) sb sk sn HK Hso Hfl) as [S1 S2].
    destruct (ealign_sound SEGS E _ (kn cs) (fst p) HK) as [[A0 A1] [q Hq]].
    assert (H8 : exists q8, bv_unsigned (edenot E (fst p)) = 8 * q8).
    { exists (q * 2 ^ (ealign (kn cs) (fst p) - 3)). rewrite Hq.
      replace (2 ^ ealign (kn cs) (fst p)) with (2 ^ (ealign (kn cs) (fst p) - 3) * 2 ^ 3) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      change (2 ^ 3) with 8. ring. }
    destruct H8 as [q8 H8].
    apply existsb_exists in Hkw as (K & HKin & HKeq). apply kentry_eqb_eq in HKeq. subst K.
    pose proof (proj1 (Forall_forall _ _) HK _ HKin) as HKW. cbn [kentry_ok] in HKW. destruct HKW as [Hflat HKW].
    pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn.
    pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
    unfold sh_lo, sh_hi, uE in Hb1, Hb2. rewrite H8 in Hb1, Hb2, S1.
    assert (E1 : 8 * q8 / 8 = q8) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
    assert (E2 : (8 * q8 + bv_unsigned (edenot E (snd p))) / 8 = q8 + bv_unsigned (edenot E (snd p)) / 8).
    { rewrite Z.add_comm, Z.mul_comm. rewrite Z.div_add by lia. lia. }
    rewrite E1 in Hb1, S1. rewrite E2 in Hb2.
    assert (Hq8 : 0 <= q8 < 2 ^ 61) by lia.
    rewrite Z.mod_small in S1 by lia.
    set (d := bv_unsigned a - estart E (SA sb sk)).
    assert (Hd : 0 <= d /\ d + Z.of_nat 1 <= elenZ E sn) by (unfold d; rewrite S1, S2; lia).
    pose proof (HKW d 1%nat (proj1 Hd) (proj2 Hd)) as Hst.
    replace (Z_to_bv 64 (estart E (SA sb sk) + d)) with a in Hst
      by (unfold d; replace (estart E (SA sb sk) + (bv_unsigned a - estart E (SA sb sk))) with (bv_unsigned a) by ring; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (hb_mr_store_ok SEGS A argH SEGS_in_hull HULL_ok argH_high E cs model FULL a 1 Hst) as [Hst' _].
    cbn [store_ok] in Hst'. unfold wview in Hst'. intros Hnone. rewrite Hnone in Hst'.
    rewrite (SEGS_in_hull a) in Hst'; [discriminate|].
    unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
End Ledger.
