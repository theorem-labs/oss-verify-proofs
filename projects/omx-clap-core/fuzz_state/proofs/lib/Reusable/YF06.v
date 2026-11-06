(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0v YK00 YK13 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0f YG00 YG0n YG0h.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition oconf (a n : Z) (o : Z * Z) : Prop := a < fst o + snd o /\ fst o < a + n.
Definition oconfb (a n : Z) (o : Z * Z) : bool := (a <? fst o + snd o) && (fst o <? a + n).
Lemma oconfb_spec : forall a n o, oconfb a n o = true <-> oconf a n o.
Proof. intros a n o. unfold oconfb, oconf. rewrite andb_true_iff, !Z.ltb_lt. tauto. Qed.
Lemma oconf_unique : forall N n o j k,
0 <= n <= N -> snd o <= N -> oconf (cand N j) n o -> oconf (cand N k) n o -> j = k.
Proof.
intros N n o j k Hn Hs [A1 A2] [B1 B2].
destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
- pose proof (cand_spacing N j k ltac:(lia) Hlt). lia.
- pose proof (cand_spacing N k j ltac:(lia) Hgt). lia.
Qed.
Lemma pick_candidateZ : forall (N n : Z) (l : list (Z * Z)) (js : list nat),
0 <= n <= N ->
Forall (fun o => snd o <= N) l ->
List.NoDup js -> (length l < length js)%nat ->
exists j, In j js /\ forall o, In o l -> ~ oconf (cand N j) n o.
Proof.
intros N n l. induction l as [|o l IH]; intros js Hn Hsz Hnd Hlen.
- destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
- inversion Hsz as [|o' l' Ho Hl]; subst.
set (js' := List.filter (fun j => negb (oconfb (cand N j) n o)) js).
assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
assert (Hlen' : (length js <= S (length js'))%nat).
{ apply filter_keep_all_but_one; [exact Hnd|].
intros j k _ _ Pj Pk. apply oconfb_spec in Pj. apply oconfb_spec in Pk.
eapply (oconf_unique N n o); eassumption. }
destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
intros q [<- | Hq].
+ intros Hc. apply oconfb_spec in Hc. rewrite Hc in Hnp. discriminate.
+ apply Hfree. exact Hq.
Qed.
Definition pieces (N : Z) (z : Z * Z) : list (Z * Z) :=
map (fun i => (fst z + Z.of_nat i * N, N)) (seq 0 (Z.to_nat ((snd z + N - 1) / N))).
Lemma pieces_len : forall N z, 0 < N -> 0 <= snd z -> Z.of_nat (length (pieces N z)) = (snd z + N - 1) / N.
Proof.
intros N z HN Hz. unfold pieces. rewrite length_map, length_seq. apply Z2Nat.id. apply Z.div_pos; lia.
Qed.
Lemma pieces_size : forall N z, Forall (fun o => snd o <= N) (pieces N z).
Proof. intros N z. unfold pieces. apply Forall_map. apply Forall_forall. intros i _. cbn [snd]. lia. Qed.
Lemma pieces_cover : forall N z a n x, 0 < N -> 0 <= n ->
fst z <= x < fst z + snd z -> a <= x < a + n ->
exists o, In o (pieces N z) /\ oconf a n o.
Proof.
intros N z a n x HN Hn Hx Ha.
set (i := (x - fst z) / N).
assert (Hi0 : 0 <= i) by (unfold i; apply Z.div_pos; lia).
pose proof (Z.div_mod (x - fst z) N ltac:(lia)) as E. pose proof (Z.mod_pos_bound (x - fst z) N HN) as B. fold i in E.
assert (Hi : i < (snd z + N - 1) / N).
{
pose proof (Z.div_mod (snd z + N - 1) N ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (snd z + N - 1) N HN) as B2.
assert (i * N < snd z) by nia. nia. }
exists (fst z + Z.of_nat (Z.to_nat i) * N, N). split.
- unfold pieces. apply in_map_iff. exists (Z.to_nat i). split; [reflexivity|]. apply in_seq. split; [lia|].
cbn [Nat.add]. apply Z2Nat.inj_lt; [lia | apply Z.div_pos; lia | exact Hi].
- unfold oconf. cbn [fst snd]. rewrite Z2Nat.id by lia. nia.
Qed.
Definition NOB : Z := 536870912.
Definition relevantb (z : Z * Z) : bool := (bottomup_floor <? fst z + snd z) && (fst z <? ASAN_CEIL).
Definition obstacles (zs : list (Z * Z)) : list (Z * Z) := flat_map (pieces NOB) (List.filter relevantb zs).
Lemma pieces_len_le : forall N z k, 0 < N -> 0 <= snd z <= k * N -> Z.of_nat (length (pieces N z)) <= k.
Proof.
intros N z k HN Hz. rewrite (pieces_len N z HN ltac:(lia)).
pose proof (Z.div_mod (snd z + N - 1) N ltac:(lia)) as E. pose proof (Z.mod_pos_bound (snd z + N - 1) N HN) as B. nia.
Qed.
Lemma obstacles_app : forall l1 l2, obstacles (l1 ++ l2) = obstacles l1 ++ obstacles l2.
Proof. intros. unfold obstacles. rewrite filter_app, flat_map_app. reflexivity. Qed.
Lemma obstacles_len : forall zs k, 0 <= k ->
Forall (fun z => relevantb z = true -> 0 <= snd z <= k * NOB) zs ->
Z.of_nat (length (obstacles zs)) <= k * Z.of_nat (length zs).
Proof.
intros zs k Hk. induction zs as [|z zs IH]; intros F; [cbn; lia|].
inversion F as [|z' zs' Fz Fzs]; subst. cbn [obstacles List.filter flat_map length].
specialize (IH Fzs). unfold obstacles in IH. rewrite Nat2Z.inj_succ.
destruct (relevantb z) eqn:R.
- cbn [flat_map]. rewrite length_app, Nat2Z.inj_add.
pose proof (pieces_len_le NOB z k ltac:(unfold NOB; lia) (Fz eq_refl)). lia.
- lia.
Qed.
Lemma obstacles_size : forall zs, Forall (fun o => snd o <= NOB) (obstacles zs).
Proof.
intros zs. unfold obstacles. apply Forall_flat_map. apply Forall_forall. intros z _. apply pieces_size.
Qed.
Lemma obstacles_free : forall zs a n (lo len : Z),
0 < n -> 0 < len -> bottomup_floor <= a -> a + n <= ASAN_CEIL ->
(forall o, In o (obstacles zs) -> ~ oconf a n o) ->
Exists (fun z => fst z <= lo /\ lo + len <= fst z + snd z) zs ->
lo + len <= a \/ a + n <= lo.
Proof.
intros zs a n lo len Hn Hlen Ha Hc Hfree Hex.
apply Exists_exists in Hex as (z & Hz & Z1 & Z2).
destruct (Z_le_gt_dec (lo + len) a) as [|G1]; [left; lia|].
destruct (Z_le_gt_dec (a + n) lo) as [|G2]; [right; lia|]. exfalso.
assert (HX : exists x, fst z <= x < fst z + snd z /\ a <= x < a + n).
{ destruct (Z_le_gt_dec lo a); [exists a | exists lo]; lia. }
destruct HX as (x & Hxz & Hxa).
assert (R : relevantb z = true).
{ unfold relevantb. apply andb_true_iff. split; apply Z.ltb_lt; lia. }
destruct (pieces_cover NOB z a n x ltac:(unfold NOB; lia) ltac:(lia) Hxz Hxa) as (o & Ho & Hconf).
apply (Hfree o); [| exact Hconf]. unfold obstacles. apply in_flat_map. exists z. split; [| exact Ho].
apply filter_In. split; [exact Hz | exact R].
Qed.
Lemma lazy_zones_len : forall ly, layout_ok ly -> Z.of_nat (length (lazy_zones ly)) <= 25.
Proof.
intros ly LY. unfold lazy_zones, static_extents, owned_extents. rewrite !length_app. cbn [length].
pose proof (proj1 (lo_extra ly LY)). lia.
Qed.
Lemma lazy_zones_relevant : forall ly, layout_ok ly ->
Forall (fun z => relevantb z = true -> 0 <= snd z <= 257 * NOB) (lazy_zones ly).
Proof.
intros ly LY. pose proof (lo_extra ly LY) as (_ & EX & _). pose proof (lo_top ly LY) as TOP. pose proof (lo_stk_ceil ly LY) as SC. pose proof (lo_img ly LY) as (J0 & J1 & J2 & J3).
pose proof bottomup_floor_val as Hfv.
apply Forall_forall. intros z Hz R. unfold lazy_zones, static_extents, owned_extents in Hz.
rewrite !in_app_iff in Hz. cbn [In] in Hz.
unfold NOB. unfold relevantb in R. apply andb_true_iff in R as [R1 R2]. apply Z.ltb_lt in R1. apply Z.ltb_lt in R2.
assert (EXz : In z (ly_extra ly) -> 0 <= snd z <= 257 * 536870912).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) EX z Hin) as (_ & He & _). lia. }
ceil; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kStoreBlockSize, kPrimResvSize, kPtrArrayResv, kCtxMapSize,
kThreadObjSize, kFakeStackSize, kNodesBlockSize, ASAN_CEIL, kImgLo, kImgEnd in *.
repeat match type of Hz with
| _ \/ _ => destruct Hz as [Hz|Hz]
| (_, _) = z => subst z; cbn [fst snd] in *
end;
try (subst z; cbn [fst snd] in *); try lia; try (exact (EXz Hz)); try (destruct Hz).
all: subst z; lia.
Qed.
Definition SEC_LIVE_N : Z := 16384.
Theorem sec_grant_exists : forall segs ly S md nZ,
layout_ok ly -> ALedger segs ly S md ->
(forall e, In e (vm_maps (m_vmmaps md)) -> 0 < bv_unsigned (snd e)) ->
Z.of_nat (length (sec_extents ly S)) <= SEC_LIVE_N ->
Forall (fun e => 0 <= snd e <= NOB) (sec_extents ly S) ->
0 < nZ <= NOB ->
exists a, grant_ok_na_pin md a nZ = true.
Proof.
intros segs ly S md nZ LY L NZ SECN SECS HnZ.
pose proof (YM05.ceil_le_top _ (al_top _ _ _ _ L)) as Htop. pose proof bottomup_floor_val as Hfv.
set (obs := obstacles (lazy_zones ly ++ sec_extents ly S)).
assert (LEN : Z.of_nat (length obs) <= 257 * 25 + SEC_LIVE_N).
{ subst obs. rewrite obstacles_app, length_app, Nat2Z.inj_add.
pose proof (obstacles_len (lazy_zones ly) 257 ltac:(lia) (lazy_zones_relevant ly LY)) as A.
pose proof (lazy_zones_len ly LY) as B.
pose proof (obstacles_len (sec_extents ly S) 1 ltac:(lia) ltac:(apply Forall_impl with (2 := SECS); intros e He _; lia)) as C. lia. }
destruct (pick_candidateZ NOB nZ obs (seq 0 (Datatypes.S (length obs))) ltac:(lia) (obstacles_size _) (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
as (j & Hj & Hfree).
apply in_seq in Hj.
set (a := cand NOB j).
assert (Ha : bottomup_floor <= a <= bottomup_floor + (257 * 25 + SEC_LIVE_N) * (2 * NOB)).
{ subst a. unfold cand. unfold NOB, SEC_LIVE_N in *. split; [nia|]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_r; [lia|]. lia. }
assert (Hce : a + nZ <= ASAN_CEIL) by (ceil; unfold ASAN_CEIL, NOB, SEC_LIVE_N in *; rewrite Hfv in Ha; lia).
exists (Z_to_bv 64 a).
unfold grant_ok_na_pin. rewrite !u64_lit by (ceil; unfold ASAN_CEIL in Hce; lia).
assert (E1 : a mod page_size = 0).
{ subst a. unfold cand. rewrite Hfv. unfold page_size, NOB. rewrite Z.add_mod by lia.
replace (Z.of_nat j * (2 * 536870912)) with ((Z.of_nat j * 262144) * 4096) by lia. rewrite Z_mod_mult. reflexivity. }
rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _)) by lia.
rewrite (proj2 (Z.leb_le _ _)) by (unfold ASAN_CEIL in Hce; lia).
rewrite YK13.region_free_app.
rewrite (al_reserved _ _ _ _ L).
replace (Z_to_bv 64 a) with (w64 a) by reflexivity. replace (Z_to_bv 64 nZ) with (w64 nZ) by reflexivity.
assert (IMGb : forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd).
{ intros sg Hsg. pose proof (al_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (lo_img ly LY) as (J0 & J1 & J2 & J3). rewrite J0 in I1, I2. unfold kImgLo in *. lia. }
rewrite (YG0h.region_free_reserved segs a nZ IMGb) by (ceil; unfold kImgEnd, ASAN_CEIL in *; lia).
rewrite (YG0h.region_free_intro); [reflexivity|].
intros e He. unfold YG0h.uw, w64. rewrite !u64_lit by (ceil; unfold ASAN_CEIL in *; lia).
apply (obstacles_free (lazy_zones ly ++ sec_extents ly S) a nZ); [lia | exact (NZ e He) | lia | exact Hce | exact Hfree | exact (al_cover _ _ _ _ L e He)].
Qed.
End b.
