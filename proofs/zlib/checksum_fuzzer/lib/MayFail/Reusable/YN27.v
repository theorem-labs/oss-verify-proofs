(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN27.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma live_bytes_app l1 l2 : State.live_bytes (l1 ++ l2) = State.live_bytes l1 + State.live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma live_bytes_nonneg l : 0 <= State.live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (u64_range n). lia. Qed.
Lemma live_bytes_iv_subtract a sz lo hi : lo <= hi -> State.live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
intros Hlh. unfold iv_subtract. pose proof (u64_range a) as Ha. pose proof (u64_range sz) as Hs.
assert (W : forall z, 0 <= z <= bv_unsigned sz -> bv_unsigned (Z_to_bv 64 z) = z).
{ intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2; cbn [app State.live_bytes];
rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; rewrite ?W; try lia.
Qed.
Lemma live_bytes_maps_subtract m lo hi : lo <= hi -> State.live_bytes (maps_subtract m lo hi) <= State.live_bytes m.
Proof.
intros H. induction m as [|[a sz] m IH]; cbn [maps_subtract State.live_bytes]; [lia|].
rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi H). lia.
Qed.
Lemma live_bytes_maps_subtract_all cuts : forall m, State.live_bytes (maps_subtract_all m cuts) <= State.live_bytes m.
Proof.
induction cuts as [|[a n] cuts IH]; intros m; cbn [maps_subtract_all]; [lia|].
pose proof (IH (maps_subtract m (bv_unsigned a) (bv_unsigned a + bv_unsigned n))).
pose proof (live_bytes_maps_subtract m (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ltac:(pose proof (u64_range n); lia)). lia.
Qed.
Lemma map_contains_subtract m lo hi a n :
map_contains m a n = true -> 0 < bv_unsigned n ->
(bv_unsigned a + bv_unsigned n <= lo \/ hi <= bv_unsigned a) -> lo <= hi ->
map_contains (maps_subtract m lo hi) a n = true.
Proof.
intros Hc Hn Hd Hlh. unfold map_contains in *. apply existsb_exists in Hc as ([b sz] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (u64_range b) as Rb. pose proof (u64_range sz) as Rs. pose proof (u64_range a) as Ra.
apply existsb_exists. induction m as [|[b' sz'] m IH]; [destruct Hin|].
cbn [maps_subtract]. destruct Hin as [E | Hin].
- injection E as -> ->. clear IH.
assert (W : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z).
{ intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
unfold iv_subtract. destruct Hd as [Hd | Hd].
+
assert (E1 : bv_unsigned b <? lo = true) by (apply Z.ltb_lt; lia). rewrite E1.
exists (b, Z_to_bv 64 (Z.min (bv_unsigned sz) (lo - bv_unsigned b))). split; [apply in_app_iff; left; apply in_app_iff; left; left; reflexivity|].
cbn [fst snd]. rewrite W by lia. apply andb_true_intro. split; apply Z.leb_le; lia.
+
assert (E2 : hi <? bv_unsigned b + bv_unsigned sz = true) by (apply Z.ltb_lt; lia). rewrite E2.
exists (Z_to_bv 64 (Z.max (bv_unsigned b) hi), Z_to_bv 64 (bv_unsigned b + bv_unsigned sz - Z.max (bv_unsigned b) hi)).
split; [apply in_app_iff; left; apply in_app_iff; right; left; reflexivity|].
cbn [fst snd]. rewrite !W by lia. apply andb_true_intro. split; apply Z.leb_le; lia.
- destruct (IH Hin) as (x & Hx & Px). exists x. split; [apply in_app_iff; right; exact Hx | exact Px].
Qed.
Lemma map_contains_remove m lo a n e :
In e m -> fst e <> lo ->
bv_unsigned (fst e) <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
map_contains (map_remove m lo) a n = true.
Proof.
intros Hin Hne H1 H2. unfold map_contains. apply existsb_exists. exists e. split.
- apply In_map_remove. auto.
- apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma length_map_remove_lt m lo e : In e m -> fst e = lo -> (length (map_remove m lo) < length m)%nat.
Proof.
intros Hin He. unfold map_remove. induction m as [|x m IH]; [destruct Hin|]. cbn [List.filter length].
destruct Hin as [-> | Hin].
- rewrite He, bv_eqb_refl. cbn [negb]. pose proof (List.filter_length_le (fun p : word * word => negb (bv_eqb (fst p) lo)) m). lia.
- specialize (IH Hin). destruct (negb (bv_eqb (fst x) lo)); cbn [length]; lia.
Qed.
Lemma map_has_In m lo n : In (lo, n) m -> map_has m lo n = true.
Proof. intros H. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact H|]. cbn. rewrite !bv_eqb_refl. reflexivity. Qed.
Lemma nslots_kill_lists : forall (l l' : list YO0i.region) r rg,
nth_error l r = Some rg -> rg_live rg = true -> rg_kind rg = RkMap ->
(forall k, nth_error l' k = if Nat.eqb k r then Some (mkRegion RkMap (rg_len rg) [] false) else nth_error l k) ->
fold_right (fun rg0 acc => region_slots rg0 + acc) 0 l' = fold_right (fun rg0 acc => region_slots rg0 + acc) 0 l - 1.
Proof.
induction l as [|x l IH]; intros l' r rg Hr Hl Hk HA'; [destruct r; discriminate|].
destruct l' as [|y l']; [specialize (HA' r); cbn in HA'; rewrite Nat.eqb_refl in HA'; destruct r; discriminate|].
destruct r as [|r].
- cbn in Hr. injection Hr as ->. pose proof (HA' 0%nat) as H0. cbn in H0. injection H0 as ->.
assert (E : l' = l) by (apply nth_error_ext; intros j; specialize (HA' (S j)); cbn in HA'; exact HA').
subst l'. cbn [fold_right]. unfold region_slots at 1 3. rewrite Hl, Hk. cbn [YO0i.rg_live]. lia.
- pose proof (HA' 0%nat) as H0. cbn in H0. injection H0 as ->. cbn [fold_right].
rewrite (IH l' r rg Hr Hl Hk) by (intros j; specialize (HA' (S j)); cbn in HA'; exact HA'). lia.
Qed.
Section d.
Variable B : malloc_syms.
Variables (L : layout) (A A' : astate) (md : Model) (r : nat) (rg : YO0i.region).
Hypothesis LG : ledger_ok B L A md.
Hypothesis LX : ledger_x L A md.
Hypothesis HL : layout_ok L A.
Hypothesis Hr : region_of A r = Some rg.
Hypothesis Hl : rg_live rg = true.
Hypothesis Hk : rg_kind rg = RkMap.
Hypothesis HA' : forall k, region_of A' k = if Nat.eqb k r then Some (mkRegion RkMap (rg_len rg) [] false) else region_of A k.
Hypothesis Hbrk : st_brk A' = st_brk A.
Hypothesis Hmd : m_vm_lazy md = [] /\ m_vm_materialized md = [].
Hypothesis Hlens : forall k rg', region_of A k = Some rg' -> rg_live rg' = true -> 0 <= rg_len rg'.
Let base := ly_reg L r.
Let len := rg_len rg.
Definition md_kill : Model := munmap_model (w64 base) (w64 len) md.
Lemma placed : base mod PGSZ = 0 /\ 4096 <= base /\ base + len <= alloc_ceiling.
Proof. destruct (lg_placed _ _ _ _ LG r rg Hr Hl) as (H1 & H2 & H3 & _). auto. Qed.
Lemma entry_in : In (w64 base, w64 len) (vm_maps (m_vmmaps md)).
Proof. apply (lg_maps _ _ _ _ LG r rg Hr Hl). rewrite Hk. discriminate. Qed.
Lemma len_pos : 0 < len /\ base + len < 2 ^ 64.
Proof.
pose proof placed as (_ & P2 & P3). pose proof alloc_ceiling_lt as ACL.
destruct (lx_maps _ _ _ LX _ entry_in) as [HH _]. unfold iv_len, w64 in HH. cbn [snd] in HH.
assert (L0 : 0 <= len) by (apply (Hlens r rg Hr Hl)).
rewrite Z_to_bv_unsigned, bv_wrap_small in HH by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
Lemma Ebase : bv_unsigned (w64 base) = base.
Proof. pose proof placed as (_&X1&X2). pose proof len_pos as [X3 X4]. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma Elen : bv_unsigned (w64 len) = len.
Proof. pose proof placed as (_&X1&X2). pose proof len_pos as [X3 X4]. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma vm_kill :
vm_maps (m_vmmaps md_kill) = map_remove (vm_maps (m_vmmaps md)) (w64 base) /\
vm_noaccess (m_vmmaps md_kill) = maps_subtract (vm_noaccess (m_vmmaps md)) base (base + len) /\
vm_reserved (m_vmmaps md_kill) = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps md_kill) = vm_limit (m_vmmaps md) /\
vm_start_brk (m_vmmaps md_kill) = vm_start_brk (m_vmmaps md) /\
vm_brk (m_vmmaps md_kill) = vm_brk (m_vmmaps md) /\
m_halted md_kill = m_halted md /\ m_vm_lazy md_kill = [] /\ m_vm_materialized md_kill = [].
Proof.
destruct Hmd as [H1 H2]. pose proof Ebase as EB. pose proof Elen as EL.
unfold md_kill, munmap_model, with_mmap_destroyed, vm_forget_range, with_vm_backing, with_vmmaps. cbn.
rewrite EB, EL, H1, H2. cbn. repeat split; reflexivity.
Qed.
Lemma other_base k rg' : k <> r -> region_of A k = Some rg' -> rg_live rg' = true -> rg_kind rg' <> RkBrk ->
w64 (ly_reg L k) <> w64 base /\ 0 < rg_len rg' /\
(ly_reg L k + rg_len rg' <= base \/ base + len <= ly_reg L k).
Proof.
intros Hne Hk' Hl' Hnb.
pose proof (lg_maps _ _ _ _ LG k rg' Hk' Hl' Hnb) as Hin'.
destruct (lg_placed _ _ _ _ LG k rg' Hk' Hl') as (_ & P2 & P3 & _). pose proof alloc_ceiling_lt.
pose proof (Hlens k rg' Hk' Hl') as L0.
destruct (lx_maps _ _ _ LX _ Hin') as [LEN' _]. unfold iv_len, w64 in LEN'. cbn [snd] in LEN'.
rewrite Z_to_bv_unsigned, bv_wrap_small in LEN' by (change (bv_modulus 64) with (2 ^ 64); lia).
pose proof len_pos as [LP _].
assert (D : ly_reg L k + rg_len rg' <= base \/ base + len <= ly_reg L k).
{ pose proof (lx_regs _ _ _ LX k r rg' rg Hne Hk' Hr Hl' Hl) as D.
unfold reg_lo in D. rewrite Hk in D. destruct (rg_kind rg') eqn:EK; [exfalso; apply Hnb; reflexivity| |];
(specialize (D ltac:(lia) ltac:(lia)); unfold ranges_disjoint in D; cbn [fst snd] in D; unfold base, len; lia). }
split; [| split; [lia | exact D]].
intros E. apply (f_equal bv_unsigned) in E. rewrite Ebase in E. unfold w64 in E.
rewrite Z_to_bv_unsigned, bv_wrap_small in E by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
Lemma fold_live_nonneg (l : list YO0i.region) :
(forall j x, nth_error l j = Some x -> rg_live x = true -> 0 <= rg_len x) ->
0 <= fold_right (fun rg0 acc => if rg_live rg0 then rg_len rg0 + acc else acc) 0 l.
Proof.
induction l as [|y l IH]; intros NN; cbn; [lia|].
assert (IH' := IH ltac:(intros j z Hj Hz; exact (NN (S j) z Hj Hz))).
destruct (rg_live y) eqn:Ey; [pose proof (NN 0%nat y eq_refl Ey); lia | lia].
Qed.
Lemma fold_live_ge (l : list YO0i.region) k x :
(forall j x, nth_error l j = Some x -> rg_live x = true -> 0 <= rg_len x) ->
nth_error l k = Some x -> rg_live x = true ->
rg_len x <= fold_right (fun rg0 acc => if rg_live rg0 then rg_len rg0 + acc else acc) 0 l.
Proof.
revert k. induction l as [|y l IH]; intros k NN Hkk Hx; [destruct k; discriminate|].
assert (NN' : forall j z, nth_error l j = Some z -> rg_live z = true -> 0 <= rg_len z) by (intros j z Hj Hz; exact (NN (S j) z Hj Hz)).
pose proof (fold_live_nonneg l NN') as SUM. cbn. destruct k as [|k].
- cbn in Hkk. injection Hkk as ->. rewrite Hx. lia.
- cbn in Hkk. pose proof (IH k NN' Hkk Hx). destruct (rg_live y) eqn:Ey; [pose proof (NN 0%nat y eq_refl Ey); lia | lia].
Qed.
Lemma live_bytes_ge k rg' : region_of A' k = Some rg' -> rg_live rg' = true -> rg_len rg' <= live_bytes A'.
Proof.
intros Hk' Hl'. unfold live_bytes. apply (fold_live_ge (st_regions A') k rg'); [| exact Hk' | exact Hl'].
intros j x Hj Hx. pose proof (HA' j) as E. unfold region_of in E at 1. rewrite Hj in E.
destruct (Nat.eqb j r); [injection E as ->; discriminate|]. symmetry in E. exact (Hlens j x E Hx).
Qed.
Theorem ledger_ok_munmap : ledger_ok B L A' md_kill.
Proof.
pose proof vm_kill as (VM & VN & VR & VL & VS & VB & _).
pose proof placed as (P1 & P2 & P3). pose proof len_pos as [LP LB]. pose proof entry_in as EIN.
assert (OTHER : forall k rg', region_of A' k = Some rg' -> rg_live rg' = true -> k <> r /\ region_of A k = Some rg').
{ intros k rg' Hk' Hl'. rewrite HA' in Hk'. destruct (Nat.eqb_spec k r); [injection Hk' as <-; discriminate | auto]. }
split.
- rewrite VR. apply LG.
- rewrite VL. apply LG.
- intros k rg' Hk' Hl' Hnb. destruct (OTHER k rg' Hk' Hl') as [Hne HkA]. rewrite VM.
apply In_map_remove. split; [apply (lg_maps _ _ _ _ LG k rg' HkA Hl' Hnb)|]. cbn [fst].
exact (proj1 (other_base k rg' Hne HkA Hl' Hnb)).
- intros k rg' off Hk' Hl' Hres Ho1 Ho2 Ho3 Hnrw. destruct (OTHER k rg' Hk' Hl') as [Hne HkA].
destruct (lg_noaccess _ _ _ _ LG k rg' off HkA Hl' Hres Ho1 Ho2 Ho3 Hnrw) as [N1 N2].
destruct (other_base k rg' Hne HkA Hl' ltac:(rewrite Hres; discriminate)) as (NB & LEN' & D).
destruct (lg_placed _ _ _ _ LG k rg' HkA Hl') as (_ & Q2 & Q3 & _). pose proof alloc_ceiling_lt.
assert (Eo : bv_unsigned (w64 (ly_reg L k + off)) = ly_reg L k + off).
{ unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). unfold PGSZ in Ho2.   lia. }
assert (Ep : bv_unsigned (w64 PGSZ) = PGSZ) by reflexivity.
rewrite VN, VM. split.
+ apply map_contains_subtract; [exact N1 | rewrite Ep; unfold PGSZ; lia | rewrite Eo, Ep | lia]. unfold PGSZ in *. lia.
+ unfold map_contains in N2. apply existsb_exists in N2 as (e & He & Pe). apply andb_prop in Pe as [Pe1 Pe2].
apply Z.leb_le in Pe1. apply Z.leb_le in Pe2. rewrite Eo, Ep in *.
apply (map_contains_remove _ _ _ _ e He); [| rewrite Eo; lia | rewrite Eo, Ep; lia].
intros Efst. destruct (lx_disj _ _ _ LX e _ He EIN) as [-> | DD].
* cbn [fst snd] in Pe1, Pe2. rewrite Ebase, Elen in *. unfold PGSZ in *. lia.
* unfold ranges_disjoint, iv_lo, iv_len in DD. cbn [fst snd] in DD. rewrite Efst, Ebase, Elen in DD.
destruct (lx_maps _ _ _ LX e He) as [Pe _]. unfold iv_len, iv_lo in *. rewrite Efst, Ebase in *. unfold PGSZ in *. lia.
- rewrite VS. apply LG.
- rewrite Hbrk, VB. apply LG.
- intros k rg' Hk' Hl'. destruct (OTHER k rg' Hk' Hl') as [_ HkA]. exact (lg_placed _ _ _ _ LG k rg' HkA Hl').
- rewrite VM. pose proof (lg_count _ _ _ _ LG) as C.
pose proof (length_map_remove_lt _ (w64 base) _ EIN eq_refl) as LT.
assert (NS : nslots A' = nslots A - 1); [| lia].
unfold nslots. apply (nslots_kill_lists _ _ r rg); assumption.
- rewrite VM. apply Forall_forall. intros e He. apply In_map_remove in He as [He Hne].
destruct (lx_in _ _ _ LX e He) as (k & rg' & Hk' & Hl' & G1 & G2).
destruct (Nat.eq_dec k r) as [->|Hkr].
+ rewrite Hr in Hk'. injection Hk' as <-. exfalso.
destruct (lx_disj _ _ _ LX e _ He EIN) as [-> | DD]; [apply Hne; reflexivity|].
unfold ranges_disjoint, iv_lo, iv_len in DD. cbn [fst snd] in DD. rewrite Ebase, Elen in DD.
destruct (lx_maps _ _ _ LX e He) as [Pe _]. unfold iv_lo, iv_len, base, len in *. lia.
+ assert (Hk'' : region_of A' k = Some rg') by (rewrite HA'; replace (Nat.eqb k r) with false by (symmetry; apply Nat.eqb_neq; exact Hkr); exact Hk').
pose proof (live_bytes_ge k rg' Hk'' Hl'). unfold iv_lo, iv_len in *. lia.
- pose proof vm_kill as (_ & _ & _ & _ & _ & _ & _ & VLZ & VMT).
unfold vm_backing_used. rewrite VLZ, VMT. cbn [length Z.of_nat maps_subtract_all Z.mul]. rewrite Z.add_0_r.
unfold vm_backed_maps. rewrite VM.
pose proof (live_bytes_maps_subtract_all (vm_noaccess (m_vmmaps md_kill)) (map_remove (vm_maps (m_vmmaps md)) (w64 base))).
pose proof (live_bytes_map_remove _ _ _ EIN) as LR. rewrite Elen in LR.
pose proof (lx_lb _ _ _ LX). rewrite (live_bytes_kill A A' r rg Hr Hl HA'). unfold len in *. lia.
-   exact (lg_ceil _ _ _ _ LG).
Qed.
Lemma md_kill_facts : m_halted md_kill = m_halted md /\ m_vm_lazy md_kill = [] /\ m_vm_materialized md_kill = [] /\
exists vm', md_kill = with_vmmaps vm' md.
Proof.
pose proof vm_kill as (_ & _ & _ & _ & _ & _ & H1 & H2 & H3). repeat split; auto.
destruct Hmd as [M1 M2]. exists (m_vmmaps md_kill). revert M1 M2 H2 H3. clear. intros M1 M2 H2 H3.
unfold md_kill, munmap_model, with_mmap_destroyed, vm_forget_range, with_vm_backing, with_vmmaps in *.
destruct md as [fd [maps lazy mat] io fs proc lim tm]. cbn in *. subst. cbn in *. reflexivity.
Qed.
End d.
End c.
