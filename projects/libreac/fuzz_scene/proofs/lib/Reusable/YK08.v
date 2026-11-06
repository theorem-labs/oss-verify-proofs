(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK08.v (donor image sha256 7093581aab04), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK06 YK10.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.
Lemma fg_u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
unfold bv_modulus. exact Hz.
Qed.
Lemma fg_alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.
Lemma fg_u64_range : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intro x. exact (bv_unsigned_in_range _ x). Qed.
Lemma page_multiple_eq : forall z, z mod page_size = 0 -> z = z / 4096 * 4096.
Proof.
intros z Hz. unfold page_size in Hz.
pose proof (Z.div_mod z 4096 ltac:(lia)). lia.
Qed.
Lemma fg_region_free_false : forall maps lo n,
region_free maps lo n = false ->
exists b s, In (b, s) maps /\ iv_overlap lo n b s = true.
Proof.
induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
cbn in H. apply andb_false_iff in H as [H|H].
- apply negb_false_iff in H. exists b, s. split; [now left|exact H].
- destruct (IH lo n H) as (b' & s' & Hin & Hov).
exists b', s'. split; [now right|exact Hov].
Qed.
Fixpoint gap_weight (nZ : Z) (l : list (word * word)) : Z :=
match l with
| [] => 0
| (_, s) :: r => bv_unsigned s + nZ + 4095 + gap_weight nZ r
end.
Lemma gap_weight_app : forall nZ l1 l2,
gap_weight nZ (l1 ++ l2) = gap_weight nZ l1 + gap_weight nZ l2.
Proof. induction l1 as [|[b s] l1 IH]; intros l2; cbn; [reflexivity|rewrite IH; lia]. Qed.
Lemma gap_weight_nonneg : forall nZ l, 0 <= nZ -> 0 <= gap_weight nZ l.
Proof.
induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ). lia.
Qed.
Definition live_at (c : Z) (p : word * word) : bool :=
c <? bv_unsigned (fst p) + bv_unsigned (snd p).
Lemma gap_weight_filter_le : forall nZ f l, 0 <= nZ ->
gap_weight nZ (List.filter f l) <= gap_weight nZ l.
Proof.
induction l as [|[b s] l IH]; intros HnZ; cbn; [lia|].
pose proof (bv_unsigned_in_range 64 s). specialize (IH HnZ).
destruct (f (b, s)); cbn; lia.
Qed.
Lemma live_weight_step : forall nZ l c c' b s,
0 <= nZ -> c <= c' ->
In (b, s) l -> live_at c (b, s) = true -> live_at c' (b, s) = false ->
gap_weight nZ (List.filter (live_at c') l) + (bv_unsigned s + nZ + 4095)
<= gap_weight nZ (List.filter (live_at c) l)
/\ (length (List.filter (live_at c') l) < length (List.filter (live_at c) l))%nat.
Proof.
intros nZ l c c' b s HnZ Hcc'.
induction l as [|[b0 s0] l IH]; intros Hin Hlive Hdead; [contradiction|].
assert (Hmono : forall p, live_at c' p = true -> live_at c p = true).
{ intros [x y] H. unfold live_at in *. cbn in *. apply Z.ltb_lt in H. apply Z.ltb_lt. lia. }
assert (Hle : gap_weight nZ (List.filter (live_at c') l) <= gap_weight nZ (List.filter (live_at c) l)
/\ (length (List.filter (live_at c') l) <= length (List.filter (live_at c) l))%nat).
{ clear IH Hin. induction l as [|[x y] l IHl]; cbn; [split; [lia|constructor]|].
pose proof (bv_unsigned_in_range 64 y).
destruct (live_at c' (x, y)) eqn:E'.
- rewrite (Hmono _ E'). cbn. destruct IHl; split; [lia|]. apply le_n_S. assumption.
- destruct (live_at c (x, y)); cbn; destruct IHl; split; try lia. }
destruct Hin as [Heq|Hin].
- injection Heq as -> ->. cbn. rewrite Hlive, Hdead. cbn.
destruct Hle as [Hw Hl]. split; [lia|]. apply Nat.lt_succ_r in Hl. exact Hl.
- destruct (IH Hin Hlive Hdead) as [Hw Hl]. cbn.
pose proof (bv_unsigned_in_range 64 s0).
destruct (live_at c' (b0, s0)) eqn:E'.
+ rewrite (Hmono _ E'). cbn. split; [lia|]. apply Nat.succ_lt_mono in Hl. exact Hl.
+ destruct (live_at c (b0, s0)); cbn; split; lia.
Qed.
Section d.
Variable L : list (word * word).
Variable nZ : Z.
Hypothesis HnZ : 0 <= nZ.
Definition scan_inv (c : Z) : Prop :=
c mod page_size = 0 /\ bottomup_floor <= c
/\ c + nZ + gap_weight nZ (List.filter (live_at c) L) <= alloc_ceiling.
Definition gap_at (c : Z) : Prop :=
c mod page_size = 0 /\ bottomup_floor <= c /\ c + nZ <= alloc_ceiling
/\ region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ) = true.
Lemma scan_ok_or_step : forall c, scan_inv c ->
gap_at c
\/ exists c', scan_inv c'
/\ (length (List.filter (live_at c') L) < length (List.filter (live_at c) L))%nat.
Proof.
intros c (Hal & Hfl & Hw).
pose proof fg_alloc_ceiling_val as Hcv. pose proof bottomup_floor_val as Hfv.
pose proof (gap_weight_nonneg nZ (List.filter (live_at c) L) HnZ) as Hw0.
assert (Hc64 : 0 <= c < 2 ^ 64) by lia.
assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply fg_u64_lit; lia).
assert (Hnu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply fg_u64_lit; lia).
destruct (region_free L (Z_to_bv 64 c) (Z_to_bv 64 nZ)) eqn:Hfree.
- left. split; [exact Hal|]. split; [exact Hfl|]. split; [lia | exact Hfree].
- right.
destruct (fg_region_free_false _ _ _ Hfree) as (b & s & Hin & Hov).
unfold iv_overlap in Hov. rewrite Hcu, Hnu in Hov.
apply andb_true_iff in Hov as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
set (B := bv_unsigned b) in *. set (S := bv_unsigned s) in *.
set (c' := page_round_up_Z (B + S)).
pose proof (page_round_up_Z_ge (B + S)) as Hge.
assert (Hle : c' <= B + S + 4095).
{ unfold c', page_round_up_Z, page_size.
pose proof (Z.mul_div_le (B + S + 4096 - 1) 4096 ltac:(lia)). lia. }
assert (Hlive : live_at c (b, s) = true) by (unfold live_at; cbn; apply Z.ltb_lt; lia).
assert (Hdead : live_at c' (b, s) = false) by (unfold live_at; cbn; apply Z.ltb_ge; lia).
destruct (live_weight_step nZ L c c' b s HnZ ltac:(lia) Hin Hlive Hdead) as [Hws Hlen].
exists c'. split; [|exact Hlen].
split; [apply page_round_up_Z_aligned|].
split; lia.
Qed.
Lemma scan : forall k c, (length (List.filter (live_at c) L) <= k)%nat -> scan_inv c ->
exists g, gap_at g.
Proof.
induction k as [|k IH]; intros c Hk Hinv.
- destruct (scan_ok_or_step c Hinv) as [Hok|(c' & _ & Hlt)]; [|lia].
exists c. exact Hok.
- destruct (scan_ok_or_step c Hinv) as [Hok|(c' & Hinv' & Hlt)].
+ exists c. exact Hok.
+ apply (IH c'); [lia|exact Hinv'].
Qed.
Theorem free_gap_of_slack :
bottomup_floor + nZ + gap_weight nZ L <= alloc_ceiling ->
exists g, g mod page_size = 0 /\ bottomup_floor <= g /\ g + nZ <= alloc_ceiling
/\ region_free L (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
intros Hslack.
assert (Hinv : scan_inv bottomup_floor).
{ split; [rewrite bottomup_floor_val; reflexivity|]. split; [lia|].
pose proof (gap_weight_filter_le nZ (live_at bottomup_floor) L HnZ). lia. }
exact (scan _ bottomup_floor (le_n _) Hinv).
Qed.
End d.
Lemma gap_weight_bound : forall nZ N l,
0 <= nZ ->
Forall (fun p => bv_unsigned (snd p) <= N) l ->
gap_weight nZ l <= Z.of_nat (length l) * (N + nZ + 4095).
Proof.
intros nZ N l HnZ H. induction H as [|[b s] l Hs _ IH]; cbn -[Z.of_nat]; [lia|].
cbn in Hs. rewrite Nat2Z.inj_succ. lia.
Qed.
Fixpoint gw_sizes (l : list (word * word)) : Z :=
match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + gw_sizes r end.
Lemma gap_weight_sizes : forall nZ l,
gap_weight nZ l = gw_sizes l + Z.of_nat (length l) * (nZ + 4095).
Proof.
intros nZ l. induction l as [|[b s] l IH]; cbn -[Z.of_nat Z.mul Z.add]; [reflexivity|].
rewrite IH, Nat2Z.inj_succ. lia.
Qed.
Theorem free_gap_of_totals : forall (h : VmMaps) nZ tot,
0 <= nZ ->
gw_sizes (vm_reserved h ++ vm_maps h) <= tot ->
bottomup_floor + nZ + tot + Z.of_nat (length (vm_reserved h ++ vm_maps h)) * (nZ + 4095) <= alloc_ceiling ->
exists g, g mod page_size = 0 /\ bottomup_floor <= g /\ g + nZ <= alloc_ceiling
/\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true
/\ hint_placement_ok_b (Z_to_bv 64 0) h g nZ = true.
Proof.
intros h nZ tot HnZ Htot Hband.
destruct (free_gap_of_slack (vm_reserved h ++ vm_maps h) nZ HnZ) as (g & Hal & Hfl & Hc & Hfree).
{ rewrite gap_weight_sizes. lia. }
exists g. split; [exact Hal|]. split; [exact Hfl|]. split; [exact Hc|]. split; [exact Hfree|].
apply hint_placement_ok_b_of_floor. exact Hfl.
Qed.
Definition ledger_split (l : list (word * word)) (K Y : Z) : Prop :=
forall b s, In (b, s) l -> bv_unsigned b + bv_unsigned s <= K \/ Y <= bv_unsigned b.
Lemma ledger_split_nil : forall K Y, ledger_split [] K Y.
Proof. intros K Y b s []. Qed.
Lemma ledger_split_mono : forall l K Y Y',
ledger_split l K Y -> Y' <= Y -> ledger_split l K Y'.
Proof. intros l K Y Y' H HY b s Hin. destruct (H b s Hin); [left|right]; lia. Qed.
Lemma ledger_split_cons : forall l K Y b s,
ledger_split l K Y ->
bv_unsigned b + bv_unsigned s <= K \/ Y <= bv_unsigned b ->
ledger_split ((b, s) :: l) K Y.
Proof.
intros l K Y b s H Hbs b' s' [Heq|Hin]; [injection Heq as <- <-; exact Hbs|].
exact (H b' s' Hin).
Qed.
Lemma ledger_split_app : forall l1 l2 K Y,
ledger_split l1 K Y -> ledger_split l2 K Y -> ledger_split (l1 ++ l2) K Y.
Proof.
intros l1 l2 K Y H1 H2 b s Hin. apply in_app_iff in Hin as [Hin|Hin]; eauto.
Qed.
Lemma ledger_split_app_inv : forall l1 l2 K Y,
ledger_split (l1 ++ l2) K Y -> ledger_split l1 K Y /\ ledger_split l2 K Y.
Proof.
intros l1 l2 K Y H. split; intros b s Hin; apply H; apply in_app_iff; auto.
Qed.
Lemma ledger_split_incl : forall l l' K Y,
ledger_split l K Y -> incl l' l -> ledger_split l' K Y.
Proof. intros l l' K Y H Hincl b s Hin. apply H. apply Hincl. exact Hin. Qed.
Lemma ledger_split_filter : forall f l K Y,
ledger_split l K Y -> ledger_split (List.filter f l) K Y.
Proof.
intros f l K Y H. apply (ledger_split_incl l); [exact H|].
intros x Hx. apply filter_In in Hx. tauto.
Qed.
Lemma ledger_split_window_free : forall l K Y nZ,
0 <= K -> 0 < nZ -> K + 2 * nZ <= Y -> Y < 2 ^ 64 ->
ledger_split l K Y ->
region_free l (Z_to_bv 64 (Y - nZ)) (Z_to_bv 64 nZ) = true.
Proof.
intros l K Y nZ HK HnZ HY HY64 Hsplit.
apply region_free_intro. intros b s Hin.
unfold iv_overlap. rewrite !fg_u64_lit by lia.
pose proof (bv_unsigned_in_range 64 s).
destruct (Hsplit b s Hin) as [Hlow|Hhigh].
- apply andb_false_iff. left. apply Z.ltb_ge. lia.
- apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Theorem null_hint_grant_above : forall h (a : word) nZ K Y,
0 < nZ -> nZ mod page_size = 0 ->
bv_unsigned a mod page_size = 0 ->
Y mod page_size = 0 -> Y <= bv_unsigned (vm_mmap_base h) ->
0 <= K -> K + 2 * nZ <= Y ->
ledger_split (vm_reserved h ++ vm_maps h) K Y ->
placement_ok_b h (bv_unsigned a) nZ = true ->
bottomup_floor <= bv_unsigned a \/ Y - 2 * nZ < bv_unsigned a.
Proof.
intros h a nZ K Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl.
pose proof (fg_u64_range a) as Ha.
pose proof (fg_u64_range (vm_mmap_base h)) as HB.
assert (HY64 : Y < 2 ^ 64) by (clear - HB HYB; lia).
assert (HgAl : (Y - nZ) mod page_size = 0).
{ rewrite Zminus_mod, HYal, HnAl. reflexivity. }
pose proof (ledger_split_window_free _ K Y nZ HK HnZ HY HY64 Hsplit) as Hfree.
apply (placement_ok_b_iff h (bv_unsigned a) nZ (proj1 Ha) HnZ HaAl HnAl) in Hpl.
clear HnAl HaAl HYal.
destruct Hpl as [Hfl|Hnhf]; [left; exact Hfl|right].
destruct (Z.lt_ge_cases (Y - 2 * nZ) (bv_unsigned a)) as [Hlt|Hge]; [exact Hlt|exfalso].
assert (H1 : bv_unsigned a + nZ <= Y - nZ) by (clear - Hge; lia).
assert (H2 : Y - nZ + nZ <= bv_unsigned (vm_mmap_base h)) by (clear - HYB; lia).
pose proof (Hnhf (Y - nZ) HgAl H1 H2) as Hno.
rewrite Hfree in Hno. discriminate.
Qed.
Theorem null_hint_grant_step : forall h (a n : word) nZ K Y,
0 < nZ -> nZ mod page_size = 0 ->
bv_unsigned a mod page_size = 0 ->
Y mod page_size = 0 -> Y <= bv_unsigned (vm_mmap_base h) ->
0 <= K -> K < bottomup_floor -> K + 2 * nZ <= Y ->
ledger_split (vm_reserved h ++ vm_maps h) K Y ->
placement_ok_b h (bv_unsigned a) nZ = true ->
let Y' := Z.min Y (bv_unsigned a) in
K < bv_unsigned a
/\ (bottomup_floor <= Y' \/ Y - 2 * nZ + page_size <= Y') /\ Y' <= Y
/\ Y' mod page_size = 0 /\ Y' <= bv_unsigned (vm_mmap_base h)
/\ ledger_split (vm_reserved h ++ (a, n) :: vm_maps h) K Y'.
Proof.
intros h a n nZ K Y HnZ HnAl HaAl HYal HYB HK HKfl HY Hsplit Hpl Y'.
pose proof (null_hint_grant_above h a nZ K Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl) as Habove.
pose proof bottomup_floor_val as Hfv.
pose proof (page_multiple_eq _ HaAl) as E1.
pose proof (page_multiple_eq _ HYal) as E2.
pose proof (page_multiple_eq _ HnAl) as E3.
clear HnAl HaAl HYal Hpl. unfold page_size.
set (qa := bv_unsigned a / 4096) in *. set (qy := Y / 4096) in *. set (qn := nZ / 4096) in *.
clearbody qa qy qn.
assert (Hqn : 1 <= qn) by lia.
assert (Hpage : bottomup_floor <= bv_unsigned a \/ Y - 2 * nZ + 4096 <= bv_unsigned a).
{ destruct Habove as [Hfl|Hlt]; [left; exact Hfl|right]. lia. }
split; [|split; [|split; [|split; [|split]]]].
- destruct Habove; lia.
- subst Y'.
destruct (Z.le_gt_cases Y (bv_unsigned a));
[rewrite Z.min_l by lia; right; lia | rewrite Z.min_r by lia; destruct Hpage; [left|right]; lia].
- lia.
- subst Y'. destruct (Z.le_gt_cases Y (bv_unsigned a)); [rewrite Z.min_l by lia | rewrite Z.min_r by lia];
[rewrite E2 | rewrite E1]; apply Z_mod_mult.
- lia.
- apply ledger_split_app_inv in Hsplit as [Hr Hm].
apply ledger_split_app; [eapply ledger_split_mono; [exact Hr|lia]|].
apply ledger_split_cons; [eapply ledger_split_mono; [exact Hm|lia]|].
right. lia.
Qed.
Definition kHighMemBeg : Z := 0x10007fff8000.
Lemma kHighMemBeg_below_mmap_base_min :
kHighMemBeg + 0x544d555f000 = mmap_base_min /\ mmap_base_min < bottomup_floor.
Proof. unfold kHighMemBeg, mmap_base_min. rewrite bottomup_floor_val. split; reflexivity. Qed.
Corollary kHighMemBeg_le : forall h (a : word) nZ Y,
0 < nZ -> nZ mod page_size = 0 ->
bv_unsigned a mod page_size = 0 ->
Y mod page_size = 0 -> Y <= bv_unsigned (vm_mmap_base h) ->
kHighMemBeg + 2 * nZ <= Y ->
ledger_split (vm_reserved h ++ vm_maps h) kHighMemBeg Y ->
placement_ok_b h (bv_unsigned a) nZ = true ->
kHighMemBeg < bv_unsigned a.
Proof.
intros h a nZ Y HnZ HnAl HaAl HYal HYB HY Hsplit Hpl.
assert (HK : 0 <= kHighMemBeg) by (unfold kHighMemBeg; clear; lia).
destruct (null_hint_grant_above h a nZ kHighMemBeg Y HnZ HnAl HaAl HYal HYB HK HY Hsplit Hpl)
as [Hfl|Hlt]; clear HnAl HaAl HYal Hpl; [|lia].
rewrite bottomup_floor_val in Hfl. unfold kHighMemBeg. lia.
Qed.
