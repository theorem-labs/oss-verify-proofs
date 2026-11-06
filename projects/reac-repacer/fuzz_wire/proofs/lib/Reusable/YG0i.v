(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0i.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the empty-depot switch (DepotCfg.depot_has_trace) taken from proofs/libreac/fuzz_knock/lib/Reusable/YG0i.v at 88154566652a, hunk by hunk (provenance evidence/depot: depot-classes.tsv, depot_apply.py): hunks 1 2 3; no hunk keeps this file's text. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/Reusable/YG0i.v at 4f87de75d677 (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0i YO0d YK04 YA0i YA0n YK0g YA06.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0s YG08 DepotCfg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YG0h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable segs : list Segment.
Variables (U : list (list Z)) (pp cc bb : Z).
Variables (ly : alayout) (S : astate) (md md' : Model).
Hypothesis LO : layout_ok ly.
Hypothesis W : WfP U pp cc bb S.
Hypothesis L : ALedger segs ly S md.
Hypothesis RES : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md).
Hypothesis LIM : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md).
Hypothesis ISP : vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md).
Hypothesis SPL : sec_placed ly S.
Variables (lo hi : Z).
Hypothesis WIN : ly_prim ly <= lo /\ lo < hi /\ hi <= ly_prim ly + kPrimResvSize.
Hypothesis CUTlo : cut_ok ly S lo.
Hypothesis CUThi : cut_ok ly S hi.
Hypothesis NOCUT : forall x, cut_ok ly S x -> ~ (lo < x < hi).
Hypothesis NZ : forall e, In e (vm_maps (m_vmmaps md)) -> 0 < uw (snd e).
Hypothesis SEPS : forall e1 e2, In e1 (vm_maps (m_vmmaps md)) -> In e2 (vm_maps (m_vmmaps md)) ->
e1 = e2 \/ uw (fst e1) + uw (snd e1) <= uw (fst e2) \/ uw (fst e2) + uw (snd e2) <= uw (fst e1).
Hypothesis NAWF : forall q, In q (vm_noaccess (m_vmmaps md)) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64.
Hypothesis VM : vm_maps (m_vmmaps md') = wiv (lo, hi - lo) :: maps_subtract (vm_maps (m_vmmaps md)) lo hi.
Hypothesis NA : vm_noaccess (m_vmmaps md') = wiv (lo, hi - lo) :: maps_subtract (vm_noaccess (m_vmmaps md)) lo hi.
Hypothesis COV : forall x, ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize) ->
YK0g.covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x.
Hypothesis EG : eager_used md' <= eager_used md.
Lemma TOPeq_r : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md).
Proof. unfold alloc_top. rewrite ISP. reflexivity. Qed.
Lemma esec_K3r : esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (sec_extents ly S) = esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S).
Proof.
apply esec_ext.
- destruct SPL as [PF _]. pose proof (sec_extents_sizes64P U pp cc bb ly S W) as SZ. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [H1 H2] & H3). pose proof (proj1 (Forall_forall _ _) SZ e He) as H4. cbn beta in H4.
clear - H1 H2 H3 H4. ceil; unfold kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *. lia.
- intros e x He Hx. apply COV. exact (sec_extents_off_prim ly S 1 ltac:(lia) SPL e x He Hx).
Qed.
Theorem ALedger_restored : ALedger segs ly S md'.
Proof.
destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
pose proof (prim_hi ly LO) as [C1 C2]. destruct WIN as (R1 & Hlh & R2).
pose proof (lo_high ly LO) as HP. unfold in_high in HP.
assert (B1 : kHighMemBeg <= ly_prim ly) by (cbn [fst snd] in HP; lia).
assert (R3 : 0 <= lo) by (unfold kHighMemBeg in B1; lia). assert (R4 : hi < 2 ^ 63) by lia.
assert (NOHOLE : forall a, ~ prim_hole_at ly S a) by (intros a; exact (wf_no_prim_hole U pp cc bb S ly a W)).
destruct L4 as (pieces & (P1 & P2 & P3) & P4).
assert (HP0 : exists P0, In P0 pieces /\ fst P0 <= lo /\ hi <= fst P0 + snd P0).
{ destruct (proj1 (Exists_exists _ _) (proj2 (P3 lo ltac:(lia)) (NOHOLE lo))) as (P0 & HP0 & Hin).
exists P0. split; [exact HP0|]. unfold in_zr in Hin. split; [lia|].
pose proof (proj1 (Forall_forall _ _) P1 P0 HP0) as (Q0 & _ & QE). pose proof (NOCUT _ QE). lia. }
destruct HP0 as (P0 & HP0 & Q1 & Q2). pose proof (proj1 (Forall_forall _ _) P1 P0 HP0) as (Q0 & QB & QE).
destruct (proj1 (P4 P0) HP0) as (V0 & _ & Q3 & Q4).
assert (UP0 : uw (fst (wiv P0)) = fst P0 /\ uw (snd (wiv P0)) = snd P0).
{ unfold wiv, uw. cbn [fst snd]. rewrite !w64_unsigned by (clear - Q0 Q3 Q4 C1 C2 B1; unfold kHighMemBeg in *; lia). auto. }
destruct UP0 as [UP1 UP2].
assert (OTHER : forall e, In e (vm_maps (m_vmmaps md)) -> e = wiv P0 \/ (uw (fst e) + uw (snd e) <= lo \/ hi <= uw (fst e))).
{ intros e He. destruct (SEPS e (wiv P0) He V0) as [E|[D|D]]; [left; exact E | right | right]; rewrite ?UP1, ?UP2 in D; lia. }
set (parts := (if fst P0 <? lo then [(fst P0, lo - fst P0)] else []) ++ (if hi <? fst P0 + snd P0 then [(hi, fst P0 + snd P0 - hi)] else [])).
set (piecesm := (lo, hi - lo) :: parts ++ List.filter (fun p => negb (fst p =? fst P0)) pieces).
assert (PARTS : forall p, In p parts <-> (fst P0 < lo /\ p = (fst P0, lo - fst P0)) \/ (hi < fst P0 + snd P0 /\ p = (hi, fst P0 + snd P0 - hi))).
{ intros p. subst parts. rewrite in_app_iff. destruct (Z.ltb_spec (fst P0) lo); destruct (Z.ltb_spec hi (fst P0 + snd P0)); cbn; intuition (try lia; try congruence). }
assert (IVS0 : iv_subtract (fst (wiv P0)) (snd (wiv P0)) lo hi = map wiv parts).
{ unfold wiv at 1 2. cbn [fst snd]. rewrite (iv_subtract_inside (fst P0) (snd P0) lo hi) by (clear - Q0 Q1 Q2 Q3 Q4 C1 C2 B1 Hlh; unfold kHighMemBeg in *; lia). subst parts.
destruct (fst P0 <? lo), (hi <? fst P0 + snd P0); reflexivity. }
assert (SAMEFST : forall p, In p pieces -> fst p = fst P0 -> p = P0).
{ intros p Hp E. destruct (pairwise_zdisjoint_In _ _ _ P2 Hp HP0) as [->|D]; [reflexivity|]. exfalso.
pose proof (proj1 (Forall_forall _ _) P1 p Hp) as (Qp & _). unfold zdisjoint in D. lia. }
assert (VM' : forall x, In x (vm_maps (m_vmmaps md')) <->
x = wiv (lo, hi - lo) \/ (In x (vm_maps (m_vmmaps md)) /\ (uw (fst x) + uw (snd x) <= lo \/ hi <= uw (fst x))) \/ In x (map wiv parts)).
{ intros x. rewrite VM. cbn [In]. rewrite maps_subtract_In. split.
- intros [E|(e & He & Hx)]; [left; symmetry; exact E|]. right. destruct (OTHER e He) as [->|D].
+ right. rewrite <- IVS0. exact Hx.
+ left. rewrite (iv_subtract_disjoint (fst e) (snd e) lo hi ltac:(lia) (NZ e He) D) in Hx. destruct Hx as [<-|[]]. destruct e; cbn; auto.
- intros [E|[[Hx D]|Hx]]; [left; symmetry; exact E | right | right].
+ exists x. split; [exact Hx|]. rewrite (iv_subtract_disjoint (fst x) (snd x) lo hi ltac:(lia) (NZ x Hx) D). left. destruct x; reflexivity.
+ exists (wiv P0). split; [exact V0|]. rewrite IVS0. exact Hx. }
assert (KEEP : forall q, In (wiv q) (vm_maps (m_vmmaps md)) -> 0 <= fst q -> 0 <= snd q -> fst q + snd q < 2 ^ 64 ->
fst q + snd q <= lo \/ hi <= fst q -> In (wiv q) (vm_maps (m_vmmaps md'))).
{ intros q Hq H1 H2 H3 D. apply (proj2 (VM' _)). right. left. split; [exact Hq|]. unfold wiv, uw. cbn [fst snd]. rewrite !w64_unsigned by lia. exact D. }
constructor; rewrite ?RES, ?LIM, ?TOPeq_r; try assumption.
-
exists piecesm. split; [split; [|split]|].
+
subst piecesm. apply Forall_cons; [cbn [fst snd]; split; [lia|]; split; [exact CUTlo | replace (lo + (hi - lo)) with hi by lia; exact CUThi]|].
apply Forall_app. split.
* apply Forall_forall. intros p Hp. apply PARTS in Hp.
destruct Hp as [[Hl ->]|[Hr ->]]; cbn [fst snd].
-- split; [lia|]. split; [exact QB|]. replace (fst P0 + (lo - fst P0)) with lo by lia. exact CUTlo.
-- split; [lia|]. split; [exact CUThi|]. replace (hi + (fst P0 + snd P0 - hi)) with (fst P0 + snd P0) by lia. exact QE.
* apply Forall_forall. intros p Hp. apply filter_In in Hp as [Hp _]. exact (proj1 (Forall_forall _ _) P1 p Hp).
+
assert (PD : forall p q, In p parts -> In q (List.filter (fun p => negb (fst p =? fst P0)) pieces) -> zdisjoint p q).
{ intros p q Hp Hq. apply PARTS in Hp. apply filter_In in Hq as [Hq NEq]. apply negb_true_iff in NEq. apply Z.eqb_neq in NEq.
destruct (pairwise_zdisjoint_In _ _ _ P2 Hq HP0) as [->|D]; [exfalso; exact (NEq eq_refl)|].
unfold zdisjoint in D |- *. destruct Hp as [[_ ->]|[_ ->]]; cbn [fst snd]; lia. }
assert (APP : forall l1 l2 : list (Z * Z), pairwise zdisjoint l1 -> pairwise zdisjoint l2 -> (forall p q, In p l1 -> In q l2 -> zdisjoint p q) -> pairwise zdisjoint (l1 ++ l2)).
{ clear. induction l1 as [|h t IH]; intros l2 P1 P2 X; cbn; [exact P2|]. destruct P1 as [F P1]. split.
- apply Forall_app. split; [exact F|]. apply Forall_forall. intros q Hq. apply X; [left; reflexivity | exact Hq].
- apply IH; [exact P1 | exact P2 |]. intros p q Hp Hq. apply X; [right; exact Hp | exact Hq]. }
subst piecesm. cbn [pairwise]. split.
* apply Forall_app. split; apply Forall_forall; intros p Hp.
-- apply PARTS in Hp. unfold zdisjoint. destruct Hp as [[_ ->]|[_ ->]]; cbn [fst snd]; lia.
-- apply filter_In in Hp as [Hp NEq]. apply negb_true_iff in NEq. apply Z.eqb_neq in NEq.
destruct (pairwise_zdisjoint_In _ _ _ P2 Hp HP0) as [->|D]; [exfalso; exact (NEq eq_refl)|]. unfold zdisjoint in D |- *. cbn [fst snd]. lia.
* apply APP; [| apply pairwise_filter; exact P2 | exact PD].
subst parts. destruct (fst P0 <? lo), (hi <? fst P0 + snd P0); cbn; repeat split; try exact I; try constructor; unfold zdisjoint; cbn [fst snd]; try lia. constructor.
+
intros a Ha. split; [intros _; exact (NOHOLE a)|]. intros _.
destruct (proj1 (Exists_exists _ _) (proj2 (P3 a Ha) (NOHOLE a))) as (p & Hp & Hap). apply Exists_exists. subst piecesm.
destruct (Z.eqb_spec (fst p) (fst P0)) as [E|NE].
* pose proof (SAMEFST p Hp E) as ->. unfold in_zr in Hap.
destruct (Z_lt_le_dec a lo) as [Y|Y].
-- exists (fst P0, lo - fst P0). split; [right; apply in_app_iff; left; apply PARTS; left; split; [lia | reflexivity] | unfold in_zr; cbn; lia].
-- destruct (Z_lt_le_dec a hi) as [Y2|Y2].
++ exists (lo, hi - lo). split; [left; reflexivity | unfold in_zr; cbn; lia].
++ exists (hi, fst P0 + snd P0 - hi). split; [right; apply in_app_iff; left; apply PARTS; right; split; [lia | reflexivity] | unfold in_zr; cbn; lia].
* exists p. split; [|exact Hap]. right. apply in_app_iff. right. apply filter_In. split; [exact Hp|]. apply negb_true_iff, Z.eqb_neq. exact NE.
+
intros p. subst piecesm. cbn [In]. rewrite in_app_iff. split.
* intros [Hp|[Hp|Hp]].
-- subst p. cbn [fst snd]. split; [apply (proj2 (VM' _)); left; reflexivity | lia].
-- pose proof Hp as Hp'. apply PARTS in Hp'.
assert (G : 0 < snd p /\ ly_prim ly <= fst p /\ fst p + snd p <= ly_prim ly + kPrimResvSize) by (destruct Hp' as [[Hl ->]|[Hl ->]]; cbn [fst snd]; clear - Hl Q0 Q1 Q2 Q3 Q4 Hlh; lia).
split; [|exact G]. apply (proj2 (VM' _)). right. right. apply in_map. exact Hp.
-- apply filter_In in Hp as [Hp NEq]. apply negb_true_iff in NEq. apply Z.eqb_neq in NEq. destruct (proj1 (P4 p) Hp) as (I1 & I2 & I3 & I4).
split; [|auto]. apply KEEP; [exact I1 | clear - I2 I3 I4 C1 C2 B1; unfold kHighMemBeg in *; lia | clear - I2 I3 I4 C1 C2 B1; unfold kHighMemBeg in *; lia | clear - I2 I3 I4 C1 C2 B1; unfold kHighMemBeg in *; lia |].
destruct (pairwise_zdisjoint_In _ _ _ P2 Hp HP0) as [->|D]; [exfalso; exact (NEq eq_refl)|]. unfold zdisjoint in D. lia.
* intros (I1 & I2 & I3 & I4).
assert (PZ : forall q : Z * Z, 0 <= fst q -> 0 <= snd q -> fst q + snd q < 2 ^ 64 -> wiv p = wiv q -> p = q).
{ intros q G1 G2 G3 E. rewrite <- (wz_wiv p) by (clear - I2 I3 I4 C1 C2 B1; unfold kHighMemBeg in *; lia). rewrite E. apply wz_wiv; lia. }
apply (proj1 (VM' _)) in I1 as [I1|[[I1 D]|I1]].
-- left. symmetry. apply PZ; cbn [fst snd]; [lia | lia | lia | exact I1].
-- right. right. assert (Hp : In p pieces) by (apply (proj2 (P4 p)); auto). apply filter_In. split; [exact Hp|]. apply negb_true_iff, Z.eqb_neq. intros E.
pose proof (SAMEFST p Hp E) as ->. rewrite UP1, UP2 in D. lia.
-- right. left. apply in_map_iff in I1 as (q & E & Hq). pose proof Hq as Hq'. apply PARTS in Hq'.
assert (EQ : p = q).
{ apply PZ; [| | | symmetry; exact E]; destruct Hq' as [[_ ->]|[_ ->]]; cbn [fst snd]; clear - Q0 Q1 Q2 Q3 Q4 R1 R2 R3 R4 C1 C2 B1 Hlh; unfold kHighMemBeg in *; lia. }
rewrite EQ. exact Hq.
-   pose proof (lo_disj ly LO) as DJ. unfold static_extents, owned_extents in DJ. cbn [pairwise app] in DJ. destruct DJ as (DP & _). apply Forall_cons_iff in DP as [DQ _].
pose proof (lo_app ly LO) as HI. unfold owned_extents in HI. apply Forall_cons_iff in HI as [_ HI]. apply Forall_cons_iff in HI as [HQ _]. unfold in_app in HQ. cbn [fst snd] in HQ, DQ.
apply KEEP; [exact L5 | cbn [fst]; clear - HQ; ceil; unfold kHighMemBeg, kLowShadowBeg in *; lia | cbn; unfold kPtrArrayResv; lia | cbn [fst snd]; clear - HQ C2; ceil; unfold kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *; lia |].
cbn [fst snd]. unfold zdisjoint in DQ. cbn [fst snd] in DQ. lia.
-   apply KEEP; [exact L6 | cbn; unfold kHighShadowBeg; lia | cbn; unfold kHighShadowBeg, kHighShadowEnd; lia | cbn [fst snd]; unfold kHighShadowBeg, kHighShadowEnd; lia |].
cbn [fst snd]. left. clear - R1 B1. unfold kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
-   intros e He. destruct SPL as [PA PD].
pose proof (proj1 (Forall_forall _ _) PA e He) as (_ & [EH1 EH2] & EC).
pose proof (proj1 (Forall_forall _ _) (sec_extents_sizes64P U pp cc bb ly S W) e He) as SZ. cbn beta in SZ.
assert (D : zdisjoint e (ly_prim ly, kPrimResvSize)).
{ clear - PD He. revert PD He. generalize (sec_extents ly S). intros l PD He. induction l as [|h t IH]; [destruct He|]. cbn in PD. destruct PD as [F PD].
destruct He as [<-|He]; [|exact (IH PD He)].
apply (proj1 (Forall_forall _ _) F). apply in_app_iff. right. unfold static_extents, owned_extents. cbn. left. reflexivity. }
apply KEEP; [exact (L7 e He) | clear - EH1 EH2 EC SZ; ceil; unfold kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *; lia | clear - SZ; lia | clear - EH1 EH2 EC SZ C2; ceil; unfold kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *; lia |].
unfold zdisjoint in D; cbn [fst snd] in D. lia.
-
intros e He. apply (proj1 (VM' _)) in He as [->|[[He _]|He]]; [| exact (L8 e He) |].
+ apply Exists_exists. exists (ly_prim ly, kPrimResvSize). split.
* unfold lazy_zones. apply in_or_app. left. cbn. do 4 right. left. reflexivity.
* unfold wiv. cbn [fst snd]. rewrite !w64_unsigned by lia. lia.
+ apply in_map_iff in He as (q & <- & Hq). apply PARTS in Hq.
pose proof (L8 (wiv P0) V0) as X. apply Exists_exists in X as (zn & Hz & Hin). apply Exists_exists. exists zn. split; [exact Hz|].
unfold wiv in Hin |- *. cbn [fst snd] in Hin |- *. rewrite !w64_unsigned in Hin by (clear - Q0 Q3 Q4 C1 C2 B1; unfold kHighMemBeg in *; lia).
destruct Hq as [[_ ->]|[_ ->]]; cbn [fst snd]; rewrite !w64_unsigned by (clear - Q0 Q1 Q2 Q3 Q4 R1 R2 R3 R4 C1 C2 B1 Hlh; unfold kHighMemBeg in *; lia); lia.
-   rewrite esec_K3r. lia.
-
intros zz Hzz. destruct (perm_facts ly 1 LO ltac:(lia) zz ltac:(lazymatch eval cbv in depot_has_trace with true => exact Hzz | false => exact (perm_live_sub ly zz Hzz) end)) as (Y1 & Y2 & Y3 & Y4). apply KEEP; [exact (L10 zz Hzz) | lia | lia | lia |].
unfold zdisjoint in Y4. cbn [fst snd] in Y4. lia.
-
intros zz Hzz. apply KEEP; [exact (L11 zz Hzz) | | | |]; unfold band_maps in Hzz; cbn [In] in Hzz;
(destruct Hzz as [<-|[<-|[<-|[]]]]; cbn [fst snd]; clear - R1 B1; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
-
destruct L15 as [N1 N2]. rewrite NA. cbn [region_free].
assert (OV : forall b s, 0 <= b -> 0 <= s -> b + s <= kHighMemBeg -> b + s < 2 ^ 64 -> negb (iv_overlap (w64 b) (w64 s) (fst (wiv (lo, hi - lo))) (snd (wiv (lo, hi - lo)))) = true).
{ intros b s Hb Hs Hbs H64. apply negb_true_iff. unfold iv_overlap, wiv. cbn [fst snd]. rewrite !w64_unsigned by lia. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
split; (apply andb_true_iff; split; [| apply region_free_subtract; [exact NAWF | assumption]]).
+ apply OV; unfold kLowShadowBeg, kLowShadowEnd, kHighMemBeg; lia.
+ apply OV; unfold kHighShadowBeg, kHighShadowEnd, kHighMemBeg; lia.
Qed.
End f.
Section g.
Variables (U : list (list Z)) (pp cc bb : Z).
Variables (ly : alayout) (S : astate) (c : Z).
Hypothesis LO : layout_ok ly.
Hypothesis W : WfP U pp cc bb S.
Hypothesis Hc : 1 <= c <= 31.
Local Abbreviation r := (reg S c).
Local Abbreviation n := kUserMapSize.
Lemma user_window :
(ly_prim ly <= addrU ly S c /\ addrU ly S c < addrU ly S c + n /\ addrU ly S c + n <= ly_prim ly + kPrimResvSize) /\
cut_ok ly S (addrU ly S c) /\ cut_ok ly S (addrU ly S c + n) /\
(forall x, cut_ok ly S x -> ~ (addrU ly S c < x < addrU ly S c + n)).
Proof.
pose proof (prim_bounds U pp cc bb ly S c LO W Hc) as (B1 & B2 & B3 & B4 & B5).
pose proof (mu_fa_facts U pp cc bb S c W Hc) as (M1 & M2 & M3 & M4).
pose proof (Z.div_exact (rg_mapped_user r) 262144 ltac:(lia)) as DX. unfold kUserMapSize in M2.
split; [| split; [| split]].
- unfold addrU, offU, kUserMapSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
- right; right. exists c. split; [exact Hc|]. left. exists (offU S c / kUserMapSize). unfold addrU, offU, kUserMapSize in *. split; lia.
- right; right. exists c. split; [exact Hc|]. left. exists (offU S c / kUserMapSize + 1). unfold addrU, offU, kUserMapSize in *. split; lia.
- exact (no_cut_inside U pp cc bb ly S c LO W Hc).
Qed.
Hypothesis HFA : rg_mapped_fa r + n <= kFreeArrayMax.
Lemma fa_window :
(ly_prim ly <= addrF ly S c /\ addrF ly S c < addrF ly S c + n /\ addrF ly S c + n <= ly_prim ly + kPrimResvSize) /\
cut_ok ly S (addrF ly S c) /\ cut_ok ly S (addrF ly S c + n) /\
(forall x, cut_ok ly S x -> ~ (addrF ly S c < x < addrF ly S c + n)).
Proof.
pose proof (prim_boundsF U pp cc bb ly S c LO W Hc HFA) as (B1 & B2 & B3 & B4 & B5).
pose proof (mu_fa_facts U pp cc bb S c W Hc) as (M1 & M2 & M3 & M4).
pose proof (Z.div_exact (rg_mapped_fa r) 262144 ltac:(lia)) as DX. unfold kFreeArrayMapSize in M4.
split; [| split; [| split]].
- unfold addrF, offF, kUserMapSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
- right; right. exists c. split; [exact Hc|]. right. exists (rg_mapped_fa r / kFreeArrayMapSize). unfold addrF, offF, fa_base, region_base, kUserMapSize, kFreeArrayMapSize in *. split; lia.
- right; right. exists c. split; [exact Hc|]. right. exists (rg_mapped_fa r / kFreeArrayMapSize + 1). unfold addrF, offF, fa_base, region_base, kUserMapSize, kFreeArrayMapSize in *. split; lia.
- exact (no_cut_insideF U pp cc bb ly S c LO W Hc HFA).
Qed.
End g.
End d.
