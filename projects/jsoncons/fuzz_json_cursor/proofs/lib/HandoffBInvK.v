(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK HandoffBridgeK HandoffLedgerK ArtRuns ArtBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma hl_minv_mono : forall A A' m, MInv A m ->
  (forall p, page_allowedb A p = true -> page_allowedb A' p = true) ->
  eager_used m + A_bytes A' <= vm_limit (m_vmmaps m) -> MInv A' m.
Proof.
  intros A A' m [N1 N2 N3 N4 N5] Hsub Hb. constructor; try assumption. intros p Hp. apply Hsub. exact (N3 p Hp).
Qed.

Lemma hl_A_bytes_app : forall A B, A_bytes (A ++ B) = A_bytes A + A_bytes B.
Proof. induction A as [|iv A IH]; intros B; cbn [A_bytes app]; [lia | rewrite IH; lia]. Qed.

Lemma hl_sum_gw : forall l, sum_sizes l = AsanPlacement.gw_sizes l.
Proof. induction l as [|q l IH]; [reflexivity|]. cbn [sum_sizes AsanPlacement.gw_sizes]. rewrite IH. reflexivity. Qed.

Definition M_LOW : amap := {| am_base := ELit 0x7fff7000; am_len := ELit 0x10000000; am_kind := KRWLAZY |}.
Definition M_GAP : amap := {| am_base := ELit 0x8fff7000; am_len := ELit 0x20000000000; am_kind := KNONELAZY |}.
Definition M_HIGH : amap := {| am_base := ELit 0x2008fff7000; am_len := ELit 0xdfff0001000; am_kind := KRWLAZY |}.

Section BInvMain.
Variable SEGS : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis IMG : img_facts SEGS A ph.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
Hypothesis HULL_below : img_hi A <= SHB_LO.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis RESV_pos : forall b s, In (b, s) (segments_reserved SEGS) -> 0 < bv_unsigned s.

Variable cs : acs.
Hypothesis NOFOG : no_fog (a_maps cs) = true.
Hypothesis HNA : hops_in_maps (a_maps cs) (a_hna cs) = true.
Hypothesis HLZ : hops_in_maps (a_maps cs) (a_hlz cs) = true.
Hypothesis VWR : forallb (vis_sh_wr A (kn cs)) (a_vis cs) = true.
Hypothesis VOFF : forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true.
Hypothesis IN_LOW : In M_LOW (a_maps cs).
Hypothesis IN_GAP : In M_GAP (a_maps cs).
Hypothesis IN_HIGH : In M_HIGH (a_maps cs).

Variable RESm : list amap.
Hypothesis RESm_in : forall m, In m RESm -> In m (a_maps cs).
Hypothesis RESm_pos : forall m, In m RESm -> exists lo, xlo (kn cs) (am_base m) = Some lo /\ 0 < lo.

Variables BUDGET LENMAX KMAX : Z.
Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
Variable EXTRA : list (Z * Z).
Hypothesis EXTRA_wf : A_wf EXTRA.
Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= LIMIT.
Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                 + (Z.of_nat (length (segments_reserved SEGS) + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

Definition resZ (E : env) (m : amap) : Z * Z := (uE E (am_base m), uE E (am_len m)).
Definition RES_of (E : env) : list (Z * Z) := map (resZ E) RESm.
Definition BASE_of : Z := a_eager cs + a_abytes cs + A_bytes EXTRA.
Definition A0_of (E : env) : list (Z * Z) := allowA A E cs ++ EXTRA.

Section Run.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : CSOK E cs R FULL model.

#[local] Notation MAPS0 := (vm_maps (m_vmmaps model)).
#[local] Notation RESV0 := (segments_reserved SEGS).
#[local] Notation NOACC0 := (vm_noaccess (m_vmmaps model)).
#[local] Notation CEIL0 := (uE E e_sp0 - 8388608).

Let Hmaps := hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC NOFOG.

Lemma hb_in_maps : forall m, In m (a_maps cs) -> In (amap_den E m) MAPS0.
Proof. intros m Hm. rewrite Hmaps. apply in_map. exact Hm. Qed.

Lemma hb_sp0_window : sp_window_lo <= uE E e_sp0 <= sp_window_hi.
Proof. exact (proj1 (proj2 (co_isp _ _ _ _ _ _ _ _ _ _ _ HC))). Qed.

Lemma hb_lit_covered : forall m BL LL x, In m (a_maps cs) -> am_base m = ELit BL -> am_len m = ELit LL -> 0 <= BL -> 0 <= LL -> BL + LL < 2 ^ 64 ->
  BL <= x < BL + LL -> BackingAlgebra.covered MAPS0 x = true.
Proof.
  intros m BL LL x Hm Hb Hl H0 H1 H2 Hx. rewrite hl_covered_in_ivs. unfold in_ivs. apply existsb_exists.
  exists (amap_den E m). split; [exact (hb_in_maps m Hm)|]. unfold amap_den. cbn [fst snd]. rewrite Hb, Hl. cbn [edenot].
  rewrite !u64_lit by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma hb_lit_entry : forall m BL LL lo hi, In m (a_maps cs) -> am_base m = ELit BL -> am_len m = ELit LL -> 0 <= BL -> 0 <= LL -> BL + LL < 2 ^ 64 ->
  BL <= lo -> hi <= BL + LL ->
  exists b s, In (b, s) MAPS0 /\ bv_unsigned b <= lo /\ hi <= bv_unsigned b + bv_unsigned s.
Proof.
  intros m BL LL lo hi Hm Hb Hl H0 H1 H2 Hlo Hhi. exists (edenot E (am_base m)), (edenot E (am_len m)).
  split; [exact (hb_in_maps m Hm)|]. rewrite Hb, Hl. cbn [edenot]. rewrite !u64_lit by lia. lia.
Qed.

Lemma hb_shrw_facts : forall x, in_shadow_rw x ->
  img_hi A <= x /\ in_ivs x NOACC0 = false.
Proof.
  intros x Hx. unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx. unfold SHB_LO in HULL_below. split; [lia|].
  assert (Hw : 0 <= x < 2 ^ 64) by lia.
  destruct Hx as [Hx|Hx].
  - destruct (hb_lazykind SEGS A LIMIT SINV argH FS0 E cs R FULL model M_LOW (Z_to_bv 64 x) HC IN_LOW eq_refl) as [Hn _].
    + cbn [M_LOW am_base am_len edenot]. rewrite !u64_lit by lia. lia.
    + rewrite u64_lit in Hn by lia. exact Hn.
  - destruct (hb_lazykind SEGS A LIMIT SINV argH FS0 E cs R FULL model M_HIGH (Z_to_bv 64 x) HC IN_HIGH eq_refl) as [Hn _].
    + cbn [M_HIGH am_base am_len edenot]. rewrite !u64_lit by lia. lia.
    + rewrite u64_lit in Hn by lia. exact Hn.
Qed.

Theorem hb_bridge_static : bridge_static SEGS MAPS0 RESV0 NOACC0 (RES_of E) CEIL0 BUDGET LENMAX KMAX.
Proof.
  pose proof hb_sp0_window as [SPlo SPhi]. unfold sp_window_lo, sp_window_hi in *.
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
  unfold SHB_LO in HULL_below.
  constructor.
  - exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)).
  - intros q Hq. exact (proj1 (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model q HC Hq)).
  - exact RESV_pos.
  - apply hl_seps_nodup; [exact (co_seps _ _ _ _ _ _ _ _ _ _ _ HC)|].
    intros q Hq. exact (proj1 (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model q HC Hq)).
  - exact (hl_seps_apart _ (co_seps _ _ _ _ _ _ _ _ _ _ _ HC)).
  - intros x Hx. destruct (hb_shrw_facts x Hx) as [Hh _].
    assert (Hw : 0 <= x < 2 ^ 64) by (unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx; lia).
    pose proof (SEGS_in_hull (Z_to_bv 64 x)) as Hs. rewrite u64_lit in Hs by lia. apply Hs.
    unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. lia.
  -
    intros Rz HR. unfold RES_of in HR. apply in_map_iff in HR as (m & <- & Hm).
    pose proof (hb_in_maps m (RESm_in m Hm)) as Hin.
    destruct (RESm_pos m Hm) as (lo & Hlo & Hpos).
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hlo) as Hb.
    destruct (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model _ HC Hin) as [P1 P2]. unfold amap_den in P1, P2. cbn [fst snd] in P1, P2.
    unfold resZ, toW. cbn [fst snd]. unfold uE. rewrite !Z_to_bv_bv_unsigned.
    split; [exact Hin|]. pose proof (u64_range (edenot E (am_base m))). pose proof (u64_range (edenot E (am_len m))). unfold uE in *. lia.
  -
    intros Rz b s HR Hbs. unfold RES_of in HR. apply in_map_iff in HR as (m & <- & Hm).
    pose proof (hb_in_maps m (RESm_in m Hm)) as Hin.
    pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) as (_ & _ & _ & P4 & _).
    pose proof (proj1 (Forall_forall _ _) RES_hull _ Hbs) as [Q1 Q2].
    unfold amap_den in P4. cbn [fst snd] in P4, Q1, Q2. unfold resZ. cbn [fst snd]. unfold uE. lia.
  -
    intros x Hx. unfold SHLO, SHHI in Hx.
    destruct (Z_lt_dec x 0x8fff7000); [|destruct (Z_lt_dec x 0x2008fff7000)].
    + apply (hb_lit_covered M_LOW _ _ x IN_LOW eq_refl eq_refl); lia.
    + apply (hb_lit_covered M_GAP _ _ x IN_GAP eq_refl eq_refl); lia.
    + apply (hb_lit_covered M_HIGH _ _ x IN_HIGH eq_refl eq_refl); lia.
  -
    intros lo hi Hlh [Hx|Hx]; unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx.
    + apply (hb_lit_entry M_LOW _ _ lo hi IN_LOW eq_refl eq_refl); lia.
    + apply (hb_lit_entry M_HIGH _ _ lo hi IN_HIGH eq_refl eq_refl); lia.
  -
    intros x b s Hx Hbs Hin. destruct (hb_shrw_facts x Hx) as [Hh _].
    pose proof (proj1 (Forall_forall _ _) RES_hull _ Hbs) as [Q1 Q2]. cbn [fst snd] in Q1, Q2. lia.
  -
    intros x Hx. rewrite hl_covered_in_ivs. exact (proj2 (hb_shrw_facts x Hx)).
  -
    rewrite <- hl_sum_gw. rewrite length_app.
    pose proof (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC) as Ht. rewrite (co_res _ _ _ _ _ _ _ _ _ _ _ HC) in Ht.
    rewrite Hmaps at 2. rewrite length_map.
    assert (0 <= LENMAX + 4095) by lia.
    assert (0 <= Z.of_nat (length RESV0) + Z.of_nat (length (a_maps cs)) + KMAX) by lia.
    rewrite Nat2Z.inj_add in GAP. nia.
  - unfold SHHI, stack_max_size. lia.
  - exact BUD.
Qed.

Theorem hb_binv_main : BInv SEGS MAPS0 RESV0 NOACC0 CEIL0 BASE_of BUDGET [] (A0_of E) FULL model.
Proof.
  clear GAP RESm_in RESm_pos IN_GAP.
  pose proof hb_sp0_window as [SPlo SPhi]. unfold sp_window_lo, sp_window_hi in *.
  assert (Hsub : forall p, page_allowedb (allowA A E cs) p = true -> page_allowedb (A0_of E) p = true).
  { intros p Hp. unfold A0_of, page_allowedb in *. rewrite existsb_app, Hp. reflexivity. }
  pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC) as He. pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC) as Ha.
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ HC) as Hl.
  assert (Hbud : eager_used model + A_bytes (A0_of E) <= BASE_of) by (unfold A0_of, BASE_of; rewrite hl_A_bytes_app; lia).
  constructor.
  - exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC).
  - unfold A0_of. apply Forall_app. split; [exact (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs) | exact EXTRA_wf].
  - apply (hl_minv_mono (allowA A E cs)); [exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hsub |]. unfold BASE_of in *. lia.
  - exact (co_wf _ _ _ _ _ _ _ _ _ _ _ HC).
  - reflexivity.
  - exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC).
  - exact (hl_alloc_top SEGS A LIMIT SINV argH FS0 E cs R FULL model HC).
  - unfold BASE_of. lia.
  - intros x Hx. exact Hx.
  - exact (hl_noacc_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model HC NOFOG HNA).
  - intros a Hp. destruct (hl_lazy_in SEGS A LIMIT SINV argH FS0 SEGS_in_hull E cs R FULL model HC NOFOG HLZ a Hp) as [H1 H2].
    rewrite hl_covered_in_ivs. split; assumption.
  - unfold live_ok. cbn. split; [intros p []|]. split; [constructor | intros p p' []].
  - intros a Hh Hna. rewrite hl_covered_in_ivs in Hna.
    apply (hl_hidden_zero SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok E cs R FULL model HC NOFOG HLZ a); [|exact Hna].
    unfold bhid, mkH in Hh |- *. apply andb_prop in Hh as [H1 H2]. rewrite H1. cbn [andb].
    apply negb_true_iff. apply negb_true_iff in H2.
    destruct (page_allowedb (allowA A E cs) (page_base a)) eqn:Hp; [|reflexivity]. rewrite (Hsub _ Hp) in H2. discriminate.
  - intros a Ha'. unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Ha'. destruct Ha' as [Hx|Hx].
    + apply (hl_shadow_defined SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high SHADOW_ok HULL_below E cs R FULL model HC NOFOG VWR VOFF
               M_LOW 0x7fff7000 0x10000000 IN_LOW eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
    + apply (hl_shadow_defined SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high SHADOW_ok HULL_below E cs R FULL model HC NOFOG VWR VOFF
               M_HIGH 0x2008fff7000 0xdfff0001000 IN_HIGH eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
  - intros w [].
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
Qed.
End Run.
End BInvMain.
