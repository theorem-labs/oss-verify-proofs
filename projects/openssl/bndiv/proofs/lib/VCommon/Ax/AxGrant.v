(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxAcct AxSys AxPostFix.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section Grant.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma in_segs_reserved (z : Z) : in_segs segs z -> inl (segments_reserved segs) z.
Proof.
  intros [sg [HIn Hz]]. exists (segment_reservation sg). split; [apply in_map; exact HIn|].
  pose proof (Hlow sg HIn) as Hl. unfold ls_beg in Hl.
  unfold bas, bsz, segment_reservation, page_round_down_Z, page_round_up_Z, page_size. cbn [fst snd].
  pose proof (N2Z.is_nonneg (seg_base sg)) as Hb. pose proof (N2Z.is_nonneg (seg_size sg)) as Hs.
  set (B := Z.of_N (seg_base sg)) in *. set (S := Z.of_N (seg_size sg)) in *.
  pose proof (Z.mul_div_le B 4096 ltac:(lia)) as D1.
  pose proof (Z.div_pos B 4096 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)) as D3.
  assert (D4 : B + S <= (B + S + 4096 - 1) / 4096 * 4096).
  { pose proof (Z.mod_pos_bound (B + S + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.div_mod (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
  rewrite !u_Z_to_bv by (unfold two64; lia). lia.
Qed.

Lemma ledger_free (h : VmMaps) (a : word) (nZ : Z) :
  vm_reserved h = segments_reserved segs -> 0 <= nZ -> bv_unsigned a + nZ <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
  forall q, bv_unsigned a <= q < bv_unsigned a + nZ -> ~ in_ledger segs h q.
Proof.
  intros Er Hn Ht Hf q Hq Hl. pose proof (alloc_top_lt h) as Hat. change two_pow_64 with two64 in Hat.
  pose proof (bv_unsigned_in_range 64 a) as Ha. change (bv_modulus 64) with two64 in Ha.
  assert (Hu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u_Z_to_bv; lia).
  assert (Hq' : bv_unsigned a <= q < bv_unsigned a + bv_unsigned (Z_to_bv 64 nZ)) by (rewrite Hu; exact Hq).
  apply (region_free_not_inl _ _ _ q Hf Hq'). apply inl_app. destruct Hl as [Hs|[Hs|Hs]].
  - left. rewrite Er. exact (in_segs_reserved q Hs).
  - lia.
  - right. exact Hs.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma seg_rom_in_segs (x : word) (b : byte) : seg_rom segs x = Some b -> in_segs segs (bv_unsigned x).
Proof.
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment segs (bv_unsigned x) 1) as [sg|] eqn:Ef; [|discriminate].
  intros _. destruct (find_segment_at' segs (bv_unsigned x) sg Ef) as [HIn Hr]. exists sg. split; [exact HIn | exact Hr].
Qed.

Lemma rv_cov (model : Model) (m : word -> option byte) (x : word) (b : byte) :
  mem_cov segs model m -> rv segs m x = Some b -> in_ledger segs (m_vmmaps model) (bv_unsigned x).
Proof.
  intros Hcov H. unfold rv in H. destruct (m x) as [b0|] eqn:E.
  - apply (mem_cov_in segs model m Hcov). rewrite E. discriminate.
  - left. exact (seg_rom_in_segs x b H).
Qed.

Lemma rv_cases (m : word -> option byte) (x : word) (b : byte) : rv segs m x = Some b -> m x <> None \/ in_segs segs (bv_unsigned x).
Proof.
  intros H. unfold rv in H. destruct (m x) as [b0|] eqn:E; [left; discriminate | right; exact (seg_rom_in_segs x b H)].
Qed.

(* [comment removed for export] *)
Lemma region_byte (ρ : valuation) (m : word -> option byte) (R : region) (z : Z) :
  region_wf ρ R -> RRegion segs ρ m R -> is_entry R = false -> in_rg ρ R z -> m (wz z) <> None \/ in_segs segs z.
Proof.
  intros Hwf HR He Hz. rewrite (RRegion_ne segs ρ m R He) in HR. unfold in_rg in Hz.
  pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hb. fold (rbase ρ R) in Hb. destruct Hwf as (W1 & W2 & _).
  assert (Hx : to_Z (of_Z (z - rbase ρ R)) = z - rbase ρ R).
  { rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  destruct (HR (of_Z (z - rbase ρ R)) ltac:(lia)) as [[b [Hrv _]] _]. rewrite Hx in Hrv.
  replace (rbase ρ R + (z - rbase ρ R)) with z in Hrv by lia.
  destruct (rv_cases m (wz z) b Hrv) as [X|X]; [left; exact X | right]. rewrite u_wz in X by (unfold two64 in *; lia). exact X.
Qed.

(* [comment removed for export] *)
Lemma region_cov (ρ : valuation) (model : Model) (m : word -> option byte) (R : region) (z : Z) :
  mem_cov segs model m -> region_wf ρ R -> RRegion segs ρ m R -> is_entry R = false -> in_rg ρ R z ->
  in_ledger segs (m_vmmaps model) z.
Proof.
  intros Hcov Hwf HR He Hz. rewrite (RRegion_ne segs ρ m R He) in HR. unfold in_rg in Hz.
  pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hb. fold (rbase ρ R) in Hb. destruct Hwf as (W1 & W2 & _).
  assert (Hx : to_Z (of_Z (z - rbase ρ R)) = z - rbase ρ R).
  { rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. }
  destruct (HR (of_Z (z - rbase ρ R)) ltac:(lia)) as [[b [Hrv _]] _]. rewrite Hx in Hrv.
  replace (rbase ρ R + (z - rbase ρ R)) with z in Hrv by lia.
  pose proof (rv_cov model m (wz z) b Hcov Hrv) as X. rewrite u_wz in X by (unfold two64 in *; lia). exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Fresh.
Variable ρ : valuation.
Variable A : list region.
Variable m : word -> option byte.
Variable model : Model.
Variables a n : Z.
Hypothesis HRM : RMem segs ρ A m.
Hypothesis Hcov : mem_cov segs model m.
Hypothesis Hcomp : comp_inv segs ρ A model.
Hypothesis Hfree : forall q, a <= q < a + n -> ~ in_ledger segs (m_vmmaps model) q.
Hypothesis Heb : forall R, In R A -> is_entry R = true -> a + n <= rbase ρ R.

(* [comment removed for export] *)
Lemma region_fresh_all : forall R, In R A -> forall z, in_rg ρ R z -> ~ (a <= z < a + n).
Proof.
  intros R HIn z Hz Hr. destruct HRM as [Hok HF].
  pose proof (regions_ok_in ρ A R Hok HIn) as Hwf. pose proof (proj1 (Forall_forall _ _) HF R HIn) as HRR.
  destruct (is_entry R) eqn:Ee.
  - pose proof (Heb R HIn Ee). unfold in_rg in Hz. lia.
  - exact (Hfree z Hr (region_cov ρ model m R z Hcov Hwf HRR Ee Hz)).
Qed.

(* [comment removed for export] *)
Lemma region_fresh : forall R, In R A -> is_shadow R = false -> forall z, in_rg ρ R z -> ~ (a <= z < a + n).
Proof.
  intros R HIn _ z Hz Hr. destruct HRM as [Hok HF].
  pose proof (regions_ok_in ρ A R Hok HIn) as Hwf. pose proof (proj1 (Forall_forall _ _) HF R HIn) as HRR.
  destruct (is_entry R) eqn:Ee.
  - pose proof (Heb R HIn Ee). unfold in_rg in Hz. lia.
  - exact (Hfree z Hr (region_cov ρ model m R z Hcov Hwf HRR Ee Hz)).
Qed.

(* [comment removed for export] *)
Lemma comp_fresh (C0 : region) : a mod 8 = 0 -> n mod 8 = 0 -> rbase ρ C0 = a / 8 + sh_off -> to_Z (rg_n C0) = n / 8 ->
  forall R, In R A -> is_shadow R = true -> forall z, in_rg ρ R z -> ~ in_rg ρ C0 z.
Proof.
  intros Ha8 Hn8 Eb En R HIn Hs z Hz Hc. unfold in_rg in Hc. rewrite Eb, En in Hc.
  destruct (Hcomp R HIn Hs z Hz) as [_ Hpre].
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. rewrite Ha8 in Da. rewrite Hn8 in Dn.
  apply (Hfree (8 * (z - sh_off))); [lia|]. apply Hpre. unfold preimage. lia.
Qed.

End Fresh.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma of_Z_small (z : Z) : 0 <= z < 2 ^ 63 -> to_Z (of_Z z) = z.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). exact H. Qed.

Lemma zero_rg_wf (ρ : valuation) (ts : terms) (o : w64) (n a : Z) :
  smod ρ ts o = a -> 0 <= n < 2 ^ 47 -> a + n <= two64 ->
  rbase ρ (zero_rg ts o n) = a /\ to_Z (rg_n (zero_rg ts o n)) = n /\ region_wf ρ (zero_rg ts o n).
Proof.
  intros Ea Hn Hw. unfold zero_rg, rbase. cbn [rg_ts rg_bo rg_n]. rewrite (of_Z_small n) by lia.
  split; [exact Ea|]. split; [reflexivity|]. destruct (depth_for_spec n ltac:(lia)) as [D1 D2].
  unfold region_wf, rbase. cbn [rg_ts rg_bo rg_n rg_d rg_kind]. rewrite (of_Z_small n) by lia. rewrite Ea.
  repeat split; try lia; try assumption. intros w i E. discriminate E.
Qed.

Lemma comp_rg_wf (ρ : valuation) (ts : terms) (o : w64) (n a : Z) :
  tdiv8_ok ts = true -> wS o mod 8 = 0 -> teval ρ ts + wS o = a -> 0 <= a -> a + n <= 2 ^ 47 -> 0 <= n ->
  rbase ρ (comp_rg ts o n) = a / 8 + sh_off /\ to_Z (rg_n (comp_rg ts o n)) = n / 8 /\ region_wf ρ (comp_rg ts o n).
Proof.
  intros Ht Ho Ea Ha Hn47 Hn.
  pose proof (Z.div_mod (wS o) 8 ltac:(lia)) as Do. rewrite Ho in Do.
  assert (Hn8 : 0 <= n / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Ha8 : a / 8 = teval ρ (tdiv8 ts) + wS o / 8).
  { rewrite <- Ea, (teval_tdiv8 ρ ts Ht). replace (8 * teval ρ (tdiv8 ts) + wS o) with (wS o + teval ρ (tdiv8 ts) * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (Hb : rbase ρ (comp_rg ts o n) = a / 8 + sh_off).
  { unfold comp_rg, rbase, smod. cbn [rg_ts rg_bo]. rewrite wZ_wofZ.
    assert (Hq : 0 <= a / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    rewrite Zplus_mod_idemp_r. rewrite Z.mod_small; [unfold sh_off in *; lia|]. unfold sh_off, two64 in *. lia. }
  split; [exact Hb|]. split; [unfold comp_rg; cbn [rg_n]; apply of_Z_small; lia|].
  destruct (depth_for_spec (n / 8) ltac:(lia)) as [D1 D2].
  unfold region_wf. rewrite Hb. unfold comp_rg. cbn [rg_ts rg_bo rg_n rg_d rg_kind]. rewrite (of_Z_small (n / 8)) by lia.
  assert (Hq : 0 <= a / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  repeat split; try lia; try assumption.
  - unfold sh_off, two64. lia.
  - intros w i E. discriminate E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma has_wit_sound (ρ : valuation) (s : store) (lo hi : Z) (A : list region) :
  sat ρ s -> 0 <= lo -> hi <= two64 -> has_wit s lo hi A = true ->
  exists W w, In W A /\ is_shadow W = true /\ in_rg ρ W w /\ lo <= w < hi.
Proof.
  intros Hs Hlo Hhi H. unfold has_wit in H. apply lexists_exists in H as [W [HIn Hw]]. unfold part_wit in Hw.
  apply andb_prop in Hw as [Hw H3]. apply andb_prop in Hw as [H1 H2]. apply Z.ltb_lt in H2.
  destruct (lrange s (wS (rg_bo W), rg_ts W)) as [[l h]|] eqn:El; [|discriminate H3].
  apply andb_prop in H3 as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
  pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr.
  assert (E : leval ρ (wS (rg_bo W), rg_ts W) = wS (rg_bo W) + teval ρ (rg_ts W)) by reflexivity. rewrite E in Hr.
  assert (Hb : rbase ρ W = wS (rg_bo W) + teval ρ (rg_ts W)).
  { unfold rbase, smod. rewrite <- (wS_mod (rg_bo W)), Zplus_mod_idemp_r. rewrite Z.mod_small; [lia|]. lia. }
  exists W, (rbase ρ W). split; [exact HIn|]. split; [exact H1|]. split; [unfold in_rg; lia | lia].
Qed.

(* [comment removed for export] *)
Lemma comp_mapped (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (a n : Z) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m ->
  has_wit s ls_beg ls_end A = true -> has_wit s hs_beg hs_hi A = true ->
  0 <= a -> 0 < n -> a + n <= 2 ^ 47 -> a mod 8 = 0 -> n mod 8 = 0 -> (a + n <= sh_lo \/ sh_hi <= a) ->
  forall z, a / 8 + sh_off <= z < a / 8 + sh_off + n / 8 -> m (wz z) <> None.
Proof.
  intros Hs HRM Hhs HL HH Ha Hn H47 Ha8 Hn8 Hside z Hz.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. rewrite Ha8 in Da. rewrite Hn8 in Dn.
  destruct Hside as [Hsd|Hsd].
  - destruct (has_wit_sound ρ s ls_beg ls_end A Hs ltac:(unfold ls_beg; lia) ltac:(unfold ls_end, two64; lia) HL) as [W [w (HIn & Hsh & Hw & Hr)]].
    apply (ss_mapped segs Hlow ρ A m W w z HRM Hhs HIn Hsh Hw). left. split; [exact Hr|].
    unfold sh_lo, sh_off, ls_beg, ls_end in *. lia.
  - destruct (has_wit_sound ρ s hs_beg hs_hi A Hs ltac:(unfold hs_beg; lia) ltac:(unfold hs_hi, two64; lia) HH) as [W [w (HIn & Hsh & Hw & Hr)]].
    apply (ss_mapped segs Hlow ρ A m W w z HRM Hhs HIn Hsh Hw). right. split; [exact Hr|].
    unfold sh_hi, sh_off, hs_beg, hs_hi in *. lia.
Qed.

End Grant.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zeros_cover_one (a n x : word) :
  zeros_cover [(a, n)] x = (bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n).
Proof. unfold zeros_cover. cbn [existsb fst snd]. rewrite orb_false_r. reflexivity. Qed.

Lemma zeros_in (m : word -> option byte) (a n : word) (z : Z) :
  bv_unsigned a <= z < bv_unsigned a + bv_unsigned n -> z < two64 -> apply_zeros m [(a, n)] (wz z) = Some (Z_to_bv 8 0).
Proof.
  intros Hz H64. pose proof (bv_unsigned_in_range 64 a) as Ha. cbn [apply_zeros]. rewrite zeros_cover_one, u_wz by (unfold two64 in *; lia).
  rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma zeros_out (m : word -> option byte) (a n x : word) :
  ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n) -> apply_zeros m [(a, n)] x = m x.
Proof.
  intros Hx. cbn [apply_zeros]. rewrite zeros_cover_one.
  destruct ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)) eqn:E; [|reflexivity].
  exfalso. apply Hx. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Lemma unmaps_in (m : word -> option byte) (a n x : word) :
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> apply_unmaps m [(a, n)] x = None.
Proof.
  intros Hx. cbn [apply_unmaps]. rewrite zeros_cover_one. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma unmaps_out (m : word -> option byte) (a n x : word) :
  ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n) -> apply_unmaps m [(a, n)] x = m x.
Proof.
  intros Hx. cbn [apply_unmaps]. rewrite zeros_cover_one.
  destruct ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)) eqn:E; [|reflexivity].
  exfalso. apply Hx. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
