(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YP09 YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0x
YO0z YO15 YO0u YO12 YO10 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN2b YN2c YN2g YN2h.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition slot_of (a : sptr) (k : Z) : sptr := padd a (AREA_HDR + META_SIZE * k).
Definition hdr_cells (a : sptr) (next : option sptr) : list mcell :=
[MCell (LMem a) 8 VSec; MCell (LMem (padd a 8)) 8 (optr next); MCell (LMem (padd a 16)) 4 (VZ METAS_PER_AREA)].
Lemma In_area_cells_split : forall s a next c,
In c (area_cells s a next) <->
In c (hdr_cells a next) \/ exists k, 0 <= k < METAS_PER_AREA /\ In c (meta_slot_cells (slot_of a k) (MT s (slot_of a k))).
Proof.
intros s a next c. unfold area_cells, hdr_cells, slot_of, MT. rewrite in_app_iff, in_flat_map. split.
- intros [H|(k & Hk & H)]; [left; exact H|]. right. apply in_seq in Hk. exists (Z.of_nat k). split; [unfold METAS_PER_AREA in *; lia | exact H].
- intros [H|(k & Hk & H)]; [left; exact H|]. right. exists (Z.to_nat k). split; [apply in_seq; lia|]. rewrite Z2Nat.id by lia. exact H.
Qed.
Lemma areas_cells_app1 : forall s l p c,
In c (areas_cells s (l ++ [p])) ->
In c (areas_cells s l) \/ (l <> [] /\ c = MCell (LMem (padd (last l (SP 0%nat 0)) 8)) 8 (VP p)) \/ In c (area_cells s p None).
Proof.
induction l as [|a t IH]; intros p c H; cbn [areas_cells app] in H.
- rewrite app_nil_r in H. right. right. exact H.
- apply in_app_iff in H as [H|H].
+ destruct t as [|b t'].
* cbn [hd_error app] in H. apply In_area_cells_split in H as [H|(k & Hk & H)].
-- cbn [hdr_cells In] in H. destruct H as [<-|[<-|[<-|[]]]].
++ left. cbn [areas_cells]. apply in_app_iff. left. apply In_area_cells_split. left. cbn. tauto.
++ right. left. split; [discriminate | reflexivity].
++ left. cbn [areas_cells]. apply in_app_iff. left. apply In_area_cells_split. left. cbn. tauto.
-- left. cbn [areas_cells]. apply in_app_iff. left. apply In_area_cells_split. right. exists k. auto.
* left. cbn [areas_cells app hd_error] in H |- *. apply in_app_iff. left. exact H.
+ destruct (IH p c H) as [H1|[[Hne ->]|H1]].
* left. cbn [areas_cells]. apply in_app_iff. right. exact H1.
* right. left. split; [discriminate|]. destruct t; [exfalso; exact (Hne eq_refl)|]. reflexivity.
* right. right. exact H1.
Qed.
Lemma areas_cells_cases : forall s s' l c,
In c (areas_cells s' l) ->
(In c (areas_cells s l) /\ exists a next, In a l /\ In c (hdr_cells a next)) \/
exists a k, In a l /\ 0 <= k < METAS_PER_AREA /\ In c (meta_slot_cells (slot_of a k) (MT s' (slot_of a k))).
Proof.
induction l as [|a t IH]; intros c H; cbn [areas_cells] in H; [destruct H|].
apply in_app_iff in H as [H|H].
- apply In_area_cells_split in H as [H|(k & Hk & H)].
+ left. split; [| exists a, (hd_error t); split; [left; reflexivity | exact H]].
cbn [areas_cells]. apply in_app_iff. left. apply In_area_cells_split. left. exact H.
+ right. exists a, k. split; [left; reflexivity|]. auto.
- destruct (IH c H) as [[H1 (a' & next & Ha' & Hh)] | (a' & k & Ha' & Hk & Hc)].
+ left. split; [cbn [areas_cells]; apply in_app_iff; right; exact H1 | exists a', next; split; [right; exact Ha' | exact Hh]].
+ right. exists a', k. split; [right; exact Ha'|]. auto.
Qed.
Lemma slot_cells_in_areas : forall s l a k c,
In a l -> 0 <= k < METAS_PER_AREA -> In c (meta_slot_cells (slot_of a k) (MT s (slot_of a k))) -> In c (areas_cells s l).
Proof.
intros s l a k c Ha Hk Hc. apply (In_areas_cells_intro s l a c Ha). intros next. apply In_area_cells_split. right. exists k. auto.
Qed.
Lemma hdr_cells_in_areas : forall s l a next c,
In a l -> In c (hdr_cells a next) -> c <> MCell (LMem (padd a 8)) 8 (optr next) -> In c (areas_cells s l).
Proof.
intros s l a next c Ha Hc Hne. apply (In_areas_cells_intro s l a c Ha). intros next'. apply In_area_cells_split. left.
cbn [hdr_cells In] in Hc |- *. destruct Hc as [<-|[<-|[<-|[]]]]; [tauto | exfalso; apply Hne; reflexivity | tauto].
Qed.
Definition nonused (x : option mslot) : Prop := match x with Some (MUsed _) => False | _ => True end.
Definition lnk_prev (x : option mslot) : sval := match x with Some (MFree pr _) => optr pr | Some (MUsed am) => optr (am_prev am) | _ => VZ 0 end.
Definition lnk_next (x : option mslot) : sval := match x with Some (MFree _ nx) => optr nx | Some (MUsed am) => optr (am_next am) | _ => VZ 0 end.
Lemma meta_slot_cells_nonused : forall q x c,
nonused x -> In c (meta_slot_cells q x) ->
c = MCell (LMem (padd q META_prev)) 8 (lnk_prev x) \/ c = MCell (LMem (padd q META_next)) 8 (lnk_next x) \/
In c [MCell (LMem (padd q META_mem)) 8 (VZ 0); MCell (LMem (padd q META_avail)) 4 (VZ 0);
MCell (LMem (padd q META_freed)) 4 (VZ 0); MCell (LMem (padd q META_bits)) 8 (VZ 0)].
Proof.
intros q x c Hn Hc. destruct x as [[pr nx| |am]|]; cbn in Hn; try contradiction; cbn [meta_slot_cells lnk_prev lnk_next] in *;
(destruct Hc as [<-|[<-|Hc]]; [left; reflexivity | right; left; reflexivity | right; right; exact Hc]).
Qed.
Lemma areas_cells_pos : forall s l c, In c (areas_cells s l) -> exists l1 a t, l = l1 ++ a :: t /\ In c (area_cells s a (hd_error t)).
Proof.
intros s l. induction l as [|a t IH]; intros c H; cbn [areas_cells] in H; [destruct H|].
apply in_app_iff in H as [H|H].
- exists [], a, t. auto.
- destruct (IH c H) as (l1 & a' & t' & -> & Hc). exists (a :: l1), a', t'. auto.
Qed.
Lemma ptr_addr_padd : forall Lx p d, ptr_addr Lx (padd p d) = ptr_addr Lx p + d.
Proof. intros Lx [r o] d. unfold ptr_addr. cbn. lia. Qed.
Lemma last_app_cons : forall (l1 : list sptr) a t d, last (l1 ++ a :: t) d = last (a :: t) d.
Proof. induction l1 as [|x l1 IH]; intros a t d; [reflexivity|]. cbn [app]. rewrite <- (IH a t d). destruct (l1 ++ a :: t) eqn:E; [destruct l1; discriminate | reflexivity]. Qed.
Lemma NoDup_last_split : forall (l1 : list sptr) a t d, NoDup (l1 ++ a :: t) -> a = last (l1 ++ a :: t) d -> t = [].
Proof.
intros l1 a t d ND E. destruct t as [|b t']; [reflexivity|]. exfalso.
rewrite last_app_cons in E. change (last (a :: b :: t') d) with (last (b :: t') d) in E.
assert (Hin : In (last (b :: t') d) (b :: t')) by (apply In_last; discriminate).
rewrite <- E in Hin. apply NoDup_app_remove_l in ND. inversion ND; subst. apply H1. exact Hin.
Qed.
Lemma NoDup_split_unique : forall (l1 l1' t t' : list sptr) a,
NoDup (l1 ++ a :: t) -> l1 ++ a :: t = l1' ++ a :: t' -> l1 = l1' /\ t = t'.
Proof.
induction l1 as [|x l1 IH]; intros [|y l1'] t t' a ND E; cbn in E, ND.
- inversion E. auto.
- inversion E. subst. exfalso. apply NoDup_cons_iff in ND as [Hn _]. apply Hn. apply in_app_iff. right. left. reflexivity.
- inversion E. subst. exfalso. apply NoDup_cons_iff in ND as [Hn _]. apply Hn. apply in_app_iff. right. left. reflexivity.
- inversion E. subst. apply NoDup_cons_iff in ND as [_ ND]. destruct (IH l1' t t' a ND H1) as [-> ->]. auto.
Qed.
Lemma flat_map_nil {T1 T2} (f : T1 -> list T2) (l : list T1) : (forall x, In x l -> f x = []) -> flat_map f l = [].
Proof. induction l as [|x l IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). cbn. apply IH. intros y Hy. apply H. right. exact Hy. Qed.
Lemma pairwise_app_inv {T} (Rl : T -> T -> Prop) : forall (u v : list T),
pairwise Rl (u ++ v) -> pairwise Rl u /\ pairwise Rl v /\ (forall x y, In x u -> In y v -> Rl x y).
Proof.
induction u as [|x u IH]; intros v H; cbn in *.
- split; [exact I|]. split; [exact H|]. intros ? ? [].
- destruct H as [H1 H2]. destruct (IH v H2) as (P1 & P2 & P3). split; [split|split].
+ intros y Hy. apply H1. apply in_app_iff. left. exact Hy.
+ exact P1.
+ exact P2.
+ intros a b [<-|Ha] Hb; [apply H1; apply in_app_iff; right; exact Hb | apply P3; assumption].
Qed.
Section a0.
Variable B : malloc_syms.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variables (L L' : layout) (A A' : astate) (mem mem' : word -> option byte) (md : Model).
Hypothesis HI : Inv X R U A.
Hypothesis XC : Xclean X A.
Hypothesis AMA : ama_ok A.
Hypothesis MID : midrep B L A mem md.
Let N := length (st_regions A).
Let MR : memrep B L A mem := mid_mem _ _ _ _ _ MID.
Let LY : layout_ok L A := mid_layout _ _ _ _ _ MID.
Let LG : ledger_ok B L A md := mid_ledger _ _ _ _ _ MID.
Let LX : ledger_x L A md := mid_ledgerx _ _ _ _ _ MID.
Let SO : syms_ok B := mid_syms _ _ _ _ _ MID.
Let PB : ptrs_below A := Inv_ptrs_below X R U A HI XC AMA.
Hypothesis UM : used_metas A' = used_metas A.
Variable newa : list sptr.
Hypothesis NA : st_areas A' = st_areas A ++ newa.
Hypothesis NA1 : forall p q l, newa = p :: q :: l -> False.
Hypothesis NDA' : NoDup (st_areas A').
Lemma newa_cases : newa = [] \/ exists p, newa = [p].
Proof. destruct newa as [|p [|q l]]; [left; reflexivity | right; exists p; reflexivity | exfalso; exact (NA1 p q l eq_refl)]. Qed.
Hypothesis RGmap : forall k rg, region_of A' k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> region_of A k = Some rg.
Hypothesis RGkeep : forall k rg, region_of A k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> region_of A' k = Some rg.
Hypothesis Lctx : ly_ctx L' = ly_ctx L.
Hypothesis Lsec : ly_sec L' = ly_sec L.
Hypothesis Lreg : forall r, (r < N)%nat -> ly_reg L' r = ly_reg L r.
Variable W : Z -> Prop.
Hypothesis Wdec : forall x, W x \/ ~ W x.
Hypothesis FR : forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Hypothesis Wmap : forall x k rg, W x -> region_of A k = Some rg -> rg_live rg = true -> rg_kind rg = RkMap ->
~ (ly_reg L k <= x < ly_reg L k + rg_len rg).
Variable Qs : list sptr.
Hypothesis Warea : forall x a, W x -> In a (st_areas A) -> ptr_addr L a <= x < ptr_addr L a + PGSZ ->
(exists q, In q Qs /\ ptr_addr L q <= x < ptr_addr L q + 16) \/
(newa <> [] /\ ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16).
Hypothesis Warea_pres : forall x a, W x -> In a (st_areas A) -> ptr_addr L a <= x < ptr_addr L a + PGSZ -> present mem' x.
Hypothesis Qs_slots : forall q, In q Qs -> exists a k, In a (st_areas A) /\ 0 <= k < METAS_PER_AREA /\ q = slot_of a k.
Hypothesis Qs_cells : forall q, In q Qs ->
nonused (MT A q) /\ nonused (MT A' q) /\
cell_mem B L' mem' (MCell (LMem (padd q META_prev)) 8 (lnk_prev (MT A' q))) /\
cell_mem B L' mem' (MCell (LMem (padd q META_next)) 8 (lnk_next (MT A' q))).
Hypothesis MT_other : forall a k, In a (st_areas A) -> 0 <= k < METAS_PER_AREA -> ~ In (slot_of a k) Qs ->
MT A' (slot_of a k) = MT A (slot_of a k).
Hypothesis NEXT_cell : forall p, newa = [p] -> st_areas A <> [] ->
cell_mem B L' mem' (MCell (LMem (padd (last (st_areas A) (SP 0%nat 0)) 8)) 8 (VP p)).
Hypothesis NEW_cells : forall p c, newa = [p] -> In c (area_cells A' p None) -> cell_mem B L' mem' c.
Hypothesis NEW_pres : forall p x, newa = [p] -> ptr_addr L' p <= x < ptr_addr L' p + PGSZ -> present mem' x.
Hypothesis CTX_cells : forall c, In c (ctx_cells A') ->
(In c (ctx_cells A) /\ forall k, (k < mc_w c)%nat -> ~ W (ms_ctx B + (match mc_loc c with LCtx o => o | _ => 0 end) + Z.of_nat k)) \/
cell_mem B L' mem' c.
Lemma loc_addr_below : forall l, (match l with LMem p => (prid p < N)%nat | LCtx _ => True end) -> loc_addr L' l = loc_addr L l.
Proof. intros [o|[k o]] H; cbn; [rewrite Lctx; reflexivity|]. cbn in H. rewrite (Lreg k H). reflexivity. Qed.
Lemma cell_mem_L' : forall m c, refs_below N c -> cell_mem B L m c -> cell_mem B L' m c.
Proof.
intros m [l w v] [H1 H2] H. unfold cell_mem in *. cbn [mc_loc mc_w mc_val] in *.
rewrite (loc_addr_below l H1). destruct v as [z|p|z|]; try exact H.
- cbn [sval_num] in *. rewrite (loc_addr_below (LMem p) H2). exact H.
- cbn [sval_num] in *. rewrite Lsec. exact H.
Qed.
Lemma old_cell : forall c, In c (image A) \/ In c (tail_cells A) ->
(forall k, (k < mc_w c)%nat -> 0 <= loc_addr L (mc_loc c) + Z.of_nat k < 2 ^ 64 /\ ~ W (loc_addr L (mc_loc c) + Z.of_nat k)) ->
cell_mem B L' mem' c.
Proof.
intros c Hc HW. apply cell_mem_L'; [apply PB; exact Hc|].
assert (H : cell_mem B L mem c).
{ destruct Hc as [Hc|Hc]; [exact (memrep_cell B L A mem c MR Hc) | exact (memrep_tail B L A mem c MR Hc)]. }
unfold cell_mem in *. destruct c as [l w v]; cbn [mc_loc mc_w mc_val] in *.
destruct v as [z|p|z|];
try (intros k Hk; destruct (HW k Hk) as [R1 R2]; unfold mbyte; rewrite (FR _ R1 R2); apply H; exact Hk).
intros Hw. destruct (H Hw) as (b & Hb & Hz). exists b. split; [|exact Hz].
destruct (HW 0%nat Hw) as [R1 R2]. rewrite Z.add_0_r in R1, R2. unfold mbyte in *. rewrite (FR _ R1 R2). exact Hb.
Qed.
Lemma region_addr : forall k rg x, region_of A k = Some rg -> rg_live rg = true ->
ly_reg L k <= x < ly_reg L k + rg_len rg -> 0 <= x < 2 ^ 64.
Proof using MID.
intros k rg x Hr Hl Hx. pose proof (lg_placed _ _ _ _ LG k rg Hr Hl) as (_ & H1 & H2 & _). pose proof (proj1 alloc_ceiling_val). lia.
Qed.
Lemma group_cell_ok : forall g am c, In (g, am) (used_metas A) -> In c (group_cells g am) -> cell_mem B L' mem' c.
Proof.
intros g am c Hg Hc. apply old_cell.
- left. unfold image. rewrite !in_app_iff. right. right. apply in_flat_map. exists (g, am). auto.
- intros k Hk. destruct (group_cell_region X R U A HI XC g am c Hg Hc) as (p & rg & El & Hr & Hkd & Hl & Ho1 & Ho2).
rewrite El. destruct p as [r o]. cbn [loc_addr prid poff] in *.
split; [apply (region_addr r rg); [exact Hr | exact Hl | lia] |].
intros HWx. exact (Wmap _ r rg HWx Hr Hl Hkd ltac:(lia)).
Qed.
Lemma tail_cell_ok : forall c, In c (tail_cells A) -> cell_mem B L' mem' c.
Proof.
intros c Hc. apply old_cell; [right; exact Hc|].
intros k Hk. destruct (tail_cell_region X R U A HI XC c Hc) as (p & rg & El & Hr & Hkd & Hl & Ho1 & Ho2).
rewrite El. destruct p as [r o]. cbn [loc_addr prid poff] in *.
split; [apply (region_addr r rg); [exact Hr | exact Hl | lia] |].
intros HWx. exact (Wmap _ r rg HWx Hr Hl Hkd ltac:(lia)).
Qed.
Lemma area_addr_old : forall a, In a (st_areas A) -> ptr_addr L' a = ptr_addr L a.
Proof using HI Lctx Lreg. intros a Ha. unfold ptr_addr. apply loc_addr_below. exact (area_prid X R U A HI a Ha). Qed.
Lemma areas_pages_disjoint : forall a1 a2, In a1 (st_areas A) -> In a2 (st_areas A) -> a1 <> a2 ->
ptr_addr L a1 + PGSZ <= ptr_addr L a2 \/ ptr_addr L a2 + PGSZ <= ptr_addr L a1.
Proof using MID.
intros a1 a2 H1 H2 Hne. destruct LY as (_ & _ & PW & _).
assert (I1 : In (LMem a1, PGSZ) (footprint A)) by (right; apply in_app_iff; left; apply in_map_iff; exists a1; auto).
assert (I2 : In (LMem a2, PGSZ) (footprint A)) by (right; apply in_app_iff; left; apply in_map_iff; exists a2; auto).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) _ _ PW I1 I2 ltac:(intros E; injection E as E1; exact (Hne E1))) as [D|D];
unfold ranges_disjoint, crange, ptr_addr in *; cbn [fst snd] in D; lia.
Qed.
Lemma area_page_addr : forall a x, In a (st_areas A) -> ptr_addr L a <= x < ptr_addr L a + PGSZ -> 0 <= x < 2 ^ 64.
Proof using HI MID.
intros a x Ha Hx. destruct (inv_areas HI) as (_ & Hareas & _).
destruct (Hareas a Ha) as (r & o & rg & -> & Ho & Hlo & Hr & Hl & Hlen & _).
unfold ptr_addr in Hx. cbn in Hx. apply (region_addr r rg x Hr Hl). unfold PGSZ in *. lia.
Qed.
Lemma last_In : forall (l : list sptr) d, l <> [] -> In (last l d) l.
Proof. intros l d H. apply In_last. exact H. Qed.
Lemma areas_nodup : NoDup (st_areas A).
Proof. exact (proj1 (inv_areas HI)). Qed.
Lemma C24 : AREA_HDR = 24. Proof. reflexivity. Qed.
Lemma C40 : META_SIZE = 40. Proof. reflexivity. Qed.
Lemma C101 : METAS_PER_AREA = 101. Proof. reflexivity. Qed.
Lemma C4096 : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma W_in_area : forall a d, In a (st_areas A) -> 0 <= d < PGSZ -> W (ptr_addr L a + d) ->
(exists k, 0 <= k < METAS_PER_AREA /\ In (slot_of a k) Qs /\ AREA_HDR + META_SIZE * k <= d < AREA_HDR + META_SIZE * k + 16) \/
(newa <> [] /\ a = last (st_areas A) (SP 0%nat 0) /\ 8 <= d < 16).
Proof.
intros a d Ha Hd HWx. rewrite C24, C40, C101. rewrite C4096 in Hd.
destruct (Warea _ a HWx Ha ltac:(rewrite C4096; lia)) as [(q & Hq & Hx) | (Hne & Hx)].
- destruct (Qs_slots q Hq) as (a' & k & Ha' & Hk & ->). unfold slot_of in Hx. rewrite ptr_addr_padd, C24, C40 in Hx. rewrite C101 in Hk.
destruct (sptr_eq_dec a' a) as [->|Hne].
+ left. exists k. split; [lia|]. split; [unfold slot_of; rewrite C24, C40; exact Hq | lia].
+ exfalso. destruct (areas_pages_disjoint a' a Ha' Ha Hne); rewrite C4096 in *; lia.
- destruct (sptr_eq_dec a (last (st_areas A) (SP 0%nat 0))) as [E|Hne2].
+ right. rewrite <- E in Hx. auto with zarith.
+ exfalso. assert (Hl : In (last (st_areas A) (SP 0%nat 0)) (st_areas A)).
{ apply In_last. intros E0. rewrite E0 in Ha. destruct Ha. }
destruct (areas_pages_disjoint a _ Ha Hl Hne2); rewrite C4096 in *; lia.
Qed.
Lemma area_cells_ok : forall c, In c (areas_cells A' (st_areas A')) -> cell_mem B L' mem' c.
Proof.
intros c Hc. rewrite NA in Hc.
destruct (areas_cells_pos A' _ c Hc) as (l1 & a & t & E & Hca).
destruct (in_dec sptr_eq_dec a (st_areas A)) as [Ha | Hnew].
2:{
assert (Hin : In a (st_areas A ++ newa)) by (rewrite E; apply in_app_iff; right; left; reflexivity).
apply in_app_iff in Hin as [Hin|Hin]; [exfalso; exact (Hnew Hin)|].
destruct newa_cases as [En | [p En]]; rewrite En in Hin; [destruct Hin|].
destruct Hin as [->|[]].
assert (Et : t = []).
{ rewrite En in E. assert (ND : NoDup (l1 ++ a :: t)) by (rewrite <- E, <- En, <- NA; exact NDA').
destruct (NoDup_split_unique l1 (st_areas A) t [] a ND (eq_sym E)) as [_ ->]. reflexivity. }
subst t. cbn [hd_error] in Hca. exact (NEW_cells a c En Hca). }
pose proof (area_addr_old a Ha) as EA.
destruct (inv_areas HI) as (_ & Hareas & _).
destruct (Hareas a Ha) as (r & o & rg & Ear & Ho & Hlo & Hr & Hl & Hlen & _).
assert (PGA : forall x, ptr_addr L a <= x < ptr_addr L a + PGSZ -> 0 <= x < 2 ^ 64) by (intros x Hx; exact (area_page_addr a x Ha Hx)).
apply In_area_cells_split in Hca as [Hh | (k & Hk & Hsl)].
-
cbn [hdr_cells In] in Hh. destruct Hh as [<-|[<-|[<-|[]]]].
+   apply old_cell.
* left. unfold image. rewrite !in_app_iff. right. left. apply (hdr_cells_in_areas A _ a None); [exact Ha | cbn; tauto | discriminate].
* intros j Hj. cbn [mc_loc mc_w] in *. change (loc_addr L (LMem a)) with (ptr_addr L a).
split; [apply PGA; rewrite C4096; lia|]. intros HWx.
destruct (W_in_area a (Z.of_nat j) Ha ltac:(rewrite C4096; lia) HWx) as [(k & Hk & _ & Hd)|(_ & _ & Hd)]; rewrite ?C24, ?C40 in Hd; lia.
+
destruct (in_split a (st_areas A) Ha) as (u & t0 & EA0).
assert (Et : t = t0 ++ newa /\ l1 = u).
{ assert (ND : NoDup (l1 ++ a :: t)) by (rewrite <- E, <- NA; exact NDA').
destruct (NoDup_split_unique l1 u t (t0 ++ newa) a ND) as [-> ->]; [| auto].
rewrite <- E, EA0, <- app_assoc. reflexivity. }
destruct Et as [Et ->].
destruct t0 as [|b t0'].
*
destruct newa_cases as [En | [p En]]; rewrite En in Et.
--
rewrite app_nil_r in Et. subst t. cbn [hd_error optr]. apply old_cell.
++ left. unfold image. rewrite !in_app_iff. right. left. rewrite EA0.
clear. induction u as [|y u IH]; cbn [areas_cells app]; apply in_app_iff; [left | right; exact IH].
apply In_area_cells_split. left. cbn. tauto.
++ intros j Hj. cbn [mc_loc mc_w] in *. change (loc_addr L (LMem (padd a 8))) with (ptr_addr L (padd a 8)). rewrite ptr_addr_padd.
split; [apply PGA; rewrite C4096; lia|]. intros HWx.
replace (ptr_addr L a + 8 + Z.of_nat j) with (ptr_addr L a + (8 + Z.of_nat j)) in HWx by lia.
destruct (W_in_area a (8 + Z.of_nat j) Ha ltac:(rewrite C4096; lia) HWx) as [(k & Hk & _ & Hd)|(Hne & _ & _)]; [rewrite ?C24, ?C40 in Hd; lia | exact (Hne En)].
--
subst t. cbn [app hd_error optr].
assert (EL : a = last (st_areas A) (SP 0%nat 0)) by (rewrite EA0, last_app_cons; reflexivity).
rewrite EL. apply (NEXT_cell p En). rewrite EA0. destruct u; discriminate.
*
assert (Hne : a <> last (st_areas A) (SP 0%nat 0)).
{ intros EL. pose proof (NoDup_last_split u a (b :: t0') (SP 0%nat 0)) as K. rewrite <- EA0 in K.
specialize (K areas_nodup EL). discriminate. }
replace (hd_error t) with (Some b) by (rewrite Et; reflexivity). cbn [optr]. apply old_cell.
-- left. unfold image. rewrite !in_app_iff. right. left. rewrite EA0.
clear. induction u as [|y u IH]; cbn [areas_cells app hd_error]; apply in_app_iff; [left | right; exact IH].
apply In_area_cells_split. left. cbn. tauto.
-- intros j Hj. cbn [mc_loc mc_w] in *. change (loc_addr L (LMem (padd a 8))) with (ptr_addr L (padd a 8)). rewrite ptr_addr_padd.
split; [apply PGA; rewrite C4096; lia|]. intros HWx.
replace (ptr_addr L a + 8 + Z.of_nat j) with (ptr_addr L a + (8 + Z.of_nat j)) in HWx by lia.
destruct (W_in_area a (8 + Z.of_nat j) Ha ltac:(rewrite C4096; lia) HWx) as [(k & Hk & _ & Hd)|(_ & EL & _)]; [rewrite ?C24, ?C40 in Hd; lia | exact (Hne EL)].
+   apply old_cell.
* left. unfold image. rewrite !in_app_iff. right. left. apply (hdr_cells_in_areas A _ a None); [exact Ha | cbn; tauto | discriminate].
* intros j Hj. cbn [mc_loc mc_w] in *. change (loc_addr L (LMem (padd a 16))) with (ptr_addr L (padd a 16)). rewrite ptr_addr_padd.
split; [apply PGA; rewrite C4096; lia|]. intros HWx.
replace (ptr_addr L a + 16 + Z.of_nat j) with (ptr_addr L a + (16 + Z.of_nat j)) in HWx by lia.
destruct (W_in_area a (16 + Z.of_nat j) Ha ltac:(rewrite C4096; lia) HWx) as [(k & Hk & _ & Hd)|(_ & _ & Hd)]; rewrite ?C24, ?C40 in Hd; lia.
-
set (q := slot_of a k) in *.
assert (Hq16 : forall j, 0 <= j < META_SIZE -> ptr_addr L q + j = ptr_addr L a + (AREA_HDR + META_SIZE * k + j))
by (intros j _; unfold q, slot_of; rewrite ptr_addr_padd; lia).
assert (WQ : forall j, 0 <= j < META_SIZE -> W (ptr_addr L q + j) -> In q Qs /\ j < 16).
{ intros j Hj HWx. rewrite Hq16 in HWx by exact Hj.
destruct (W_in_area a (AREA_HDR + META_SIZE * k + j) Ha ltac:(rewrite C24, C40, C4096, C101 in *; lia) HWx) as [(k' & Hk' & Hin' & Hd)|(_ & _ & Hd)];
rewrite ?C24, ?C40, ?C101 in *; [|lia].
assert (k' = k) by lia. subst k'. split; [exact Hin' | lia]. }
assert (QA : forall j, 0 <= j < META_SIZE -> 0 <= ptr_addr L q + j < 2 ^ 64).
{ intros j Hj. rewrite Hq16 by exact Hj. apply PGA. rewrite C24, C40, C4096, C101 in *. lia. }
destruct (in_dec sptr_eq_dec q Qs) as [Hin | Hnin].
+
destruct (Qs_cells q Hin) as (N0 & N1 & CP & CN).
destruct (meta_slot_cells_nonused q (MT A' q) c N1 Hsl) as [-> | [-> | Hz]]; [exact CP | exact CN |].
apply old_cell.
* left. unfold image. rewrite !in_app_iff. right. left. apply (slot_cells_in_areas A _ a k); [exact Ha | exact Hk|]. fold q.
destruct (MT A q) as [[pr nx| |am]|]; cbn in N0; try contradiction; cbn [meta_slot_cells In]; cbn [In] in Hz; tauto.
* intros j Hj. cbn [In] in Hz.
destruct Hz as [<-|[<-|[<-|[<-|[]]]]]; cbn [mc_loc mc_w] in Hj |- *;
match goal with |- context [loc_addr L (LMem (padd q ?d))] =>
change (loc_addr L (LMem (padd q d))) with (ptr_addr L (padd q d)); rewrite ptr_addr_padd;
replace (ptr_addr L q + d + Z.of_nat j) with (ptr_addr L q + (d + Z.of_nat j)) by lia end;
unfold META_mem, META_avail, META_freed, META_bits in *;
(split; [apply QA; rewrite C40; lia | intros HWx;
match type of HWx with W (ptr_addr L q + ?e) =>
assert (Hrj : 0 <= e < META_SIZE) by (rewrite C40; lia); destruct (WQ e Hrj HWx) as [_ Hj']; lia end]).
+
pose proof (MT_other a k Ha Hk Hnin) as EMT. fold q in EMT. rewrite EMT in Hsl.
apply old_cell.
* left. unfold image. rewrite !in_app_iff. right. left. apply (slot_cells_in_areas A _ a k); [exact Ha | exact Hk | exact Hsl].
* intros j Hj. destruct (In_meta_slot_cells q _ c Hsl) as (d & El & Hd1 & Hd2). rewrite El.
change (loc_addr L (LMem (padd q d))) with (ptr_addr L (padd q d)). rewrite ptr_addr_padd.
replace (ptr_addr L q + d + Z.of_nat j) with (ptr_addr L q + (d + Z.of_nat j)) by lia.
split; [apply QA; lia|]. intros HWx. destruct (WQ (d + Z.of_nat j) ltac:(lia) HWx) as [Hin' _]. exact (Hnin Hin').
Qed.
Lemma ctx_cell_ok : forall c, In c (ctx_cells A') -> cell_mem B L' mem' c.
Proof.
intros c Hc. destruct (CTX_cells c Hc) as [[Hold HW] | H]; [|exact H].
destruct (In_ctx_cells A c Hold) as (off & El & Ho1 & Ho2).
apply old_cell; [left; unfold image; apply in_app_iff; left; exact Hold|].
intros k Hk. rewrite El. cbn [loc_addr]. rewrite (mid_ctx _ _ _ _ _ MID).
pose proof (so_ctx_lo _ SO). pose proof (so_ctx_hi _ SO). pose proof (proj1 alloc_ceiling_val).
split; [lia|]. rewrite El in HW. exact (HW k Hk).
Qed.
Lemma footprint_ok : Forall (foot_ok L' mem') (footprint A').
Proof.
apply Forall_forall. intros e He.
destruct (In_footprint_inv A' e He) as [-> | [(a & Ha & ->) | (k & rg & Hr & Hk & Hl & ->)]]; [exact I| |]; cbn [foot_ok fst snd].
- rewrite NA in Ha. apply in_app_iff in Ha as [Ha | Ha].
+ change (loc_addr L' (LMem a)) with (ptr_addr L' a). rewrite (area_addr_old a Ha). intros x Hx.
destruct (MR) as (_ & _ & FT).
assert (Hin : In (LMem a, PGSZ) (footprint A)) by (right; apply in_app_iff; left; apply in_map_iff; exists a; auto).
pose proof (proj1 (Forall_forall _ _) FT _ Hin) as F. cbn [foot_ok fst snd] in F. change (loc_addr L (LMem a)) with (ptr_addr L a) in F.
pose proof (area_page_addr a x Ha Hx) as Hx64.
destruct (Wdec x) as [HWx | HnW].
* exact (Warea_pres x a HWx Ha Hx).
* destruct (F x Hx) as [b Hb]. exists b. rewrite (FR x Hx64 HnW). exact Hb.
+ destruct newa_cases as [En | [p En]]; rewrite En in Ha; [destruct Ha|]. destruct Ha as [<-|[]].
intros x Hx. exact (NEW_pres p x En Hx).
- pose proof (RGmap k rg Hr Hl Hk) as HrA.
assert (HkN : (k < N)%nat) by exact (region_of_lt _ _ _ HrA).
cbn [loc_addr]. rewrite (Lreg k HkN), Z.add_0_r. intros x Hx.
pose proof (region_addr k rg x HrA Hl Hx) as Hx64.
assert (HnW : ~ W x) by (intros HWx; exact (Wmap x k rg HWx HrA Hl Hk Hx)).
destruct (memrep_present B L A mem k rg x MR HrA Hk Hl Hx) as [b Hb]. exists b. rewrite (FR x Hx64 HnW). exact Hb.
Qed.
Theorem memrep_xfer : memrep B L' A' mem'.
Proof using HI XC AMA MID UM NA NA1 NDA' RGmap RGkeep Lctx Lsec Lreg Wdec FR Wmap Warea Warea_pres Qs_slots Qs_cells MT_other NEXT_cell NEW_cells NEW_pres CTX_cells.
split; [|split].
- apply Forall_forall. intros c Hc. unfold image in Hc. rewrite !in_app_iff in Hc. destruct Hc as [Hc|[Hc|Hc]].
+ exact (ctx_cell_ok c Hc).
+ exact (area_cells_ok c Hc).
+ apply in_flat_map in Hc as ([g am] & Hg & Hc). rewrite UM in Hg. exact (group_cell_ok g am c Hg Hc).
- apply Forall_forall. intros c Hc. unfold tail_cells in Hc. rewrite UM in Hc. exact (tail_cell_ok c Hc).
- exact footprint_ok.
Qed.
Theorem tail_geom_xfer : tail_geom L' A'.
Proof using HI XC MID UM RGkeep Lctx Lreg.
pose proof (mid_tailg _ _ _ _ _ MID) as TG. unfold tail_geom in *. unfold tail_cells in *. rewrite UM.
rewrite Forall_forall in TG |- *. intros c Hc k Hk. specialize (TG c Hc k Hk).
fold (tail_cells A) in Hc.
destruct (tail_cell_region X R U A HI XC c Hc) as (p & rg & El & Hr & Hkd & Hl & Ho1 & Ho2).
assert (EL : loc_addr L' (mc_loc c) = loc_addr L (mc_loc c)).
{ apply loc_addr_below. rewrite El. exact (region_of_lt _ _ _ Hr). }
rewrite EL. destruct TG as [[e [He Hx]] Hnb]. split.
- exists (LMem (SP (prid p) 0), rg_len rg). split.
+ apply (footprint_region_In A' (prid p) rg); [apply RGkeep; assumption | exact Hkd | exact Hl].
+ cbn [fst snd loc_addr]. rewrite (Lreg (prid p) (region_of_lt _ _ _ Hr)), Z.add_0_r.
rewrite El. destruct p as [r o]. cbn [loc_addr prid poff] in *. lia.
- intros (b & Hb & Hbx). apply Hnb. exists b.
assert (UB : user_blocks A' = user_blocks A) by (unfold user_blocks; rewrite UM; reflexivity).
rewrite UB in Hb. split; [exact Hb|].
destruct b as [q n]. cbn [fst snd] in *.
assert (Hq : (prid q < N)%nat).
{ unfold user_blocks in Hb. apply in_flat_map in Hb as ([g am] & Hg & Hb). cbn [snd] in Hb.
apply in_flat_map in Hb as (i & Hi & Hb). destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hb].
destruct (fr_kind fr); [|destruct Hb]. destruct Hb as [E|[]]. injection E as <- <-.
unfold slot_start. rewrite !YO0u.prid_padd. apply (used_prid X R U A HI g). apply (used_metas_usedX' X R U A HI XC). exact Hg. }
rewrite (loc_addr_below (LMem q) Hq) in Hbx. exact Hbx.
Qed.
Definition regions_part (s : astate) : list (loc * Z) :=
flat_map (fun k => match region_of s k with
| Some rg => match rg_kind rg with
| RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else []
| _ => []
end
| None => []
end) (seq 0 (length (st_regions s))).
Lemma footprint_split : forall s, footprint s = ((LCtx 0, CTX_SIZE) :: map (fun a => (LMem a, PGSZ)) (st_areas s)) ++ regions_part s.
Proof. intros s. reflexivity. Qed.
Hypothesis LEN : (N <= length (st_regions A'))%nat.
Lemma regions_part_same : regions_part A' = regions_part A.
Proof.
unfold regions_part.
set (f := fun s k => match region_of s k with
| Some rg => match rg_kind rg with RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else [] | _ => [] end
| None => [] end).
change (flat_map (f A') (seq 0 (length (st_regions A'))) = flat_map (f A) (seq 0 N)).
assert (K : forall k, f A' k = f A k).
{ intros k. unfold f. destruct (region_of A' k) as [rg'|] eqn:E'.
- destruct (region_of A k) as [rg|] eqn:E.
+ destruct (rg_kind rg) eqn:Ek2; [| | destruct (rg_live rg) eqn:El2].
* destruct (rg_kind rg') eqn:Ek; try reflexivity. destruct (rg_live rg') eqn:El; [|reflexivity].
pose proof (RGmap k rg' E' El Ek) as X2. rewrite E in X2. injection X2 as ->. congruence.
* destruct (rg_kind rg') eqn:Ek; try reflexivity. destruct (rg_live rg') eqn:El; [|reflexivity].
pose proof (RGmap k rg' E' El Ek) as X2. rewrite E in X2. injection X2 as ->. congruence.
* pose proof (RGkeep k rg E El2 Ek2) as X2. rewrite E' in X2. injection X2 as ->. rewrite Ek2, El2. reflexivity.
* destruct (rg_kind rg') eqn:Ek; try reflexivity. destruct (rg_live rg') eqn:El; [|reflexivity].
pose proof (RGmap k rg' E' El Ek) as X2. rewrite E in X2. injection X2 as ->. congruence.
+ destruct (rg_kind rg') eqn:Ek; try reflexivity. destruct (rg_live rg') eqn:El; [|reflexivity].
pose proof (RGmap k rg' E' El Ek) as X2. rewrite E in X2. discriminate.
- destruct (region_of A k) as [rg|] eqn:E; [|reflexivity].
destruct (rg_kind rg) eqn:Ek2; try reflexivity; destruct (rg_live rg) eqn:El2; try reflexivity.
pose proof (RGkeep k rg E El2 Ek2) as X2. rewrite E' in X2. discriminate. }
replace (length (st_regions A')) with (N + (length (st_regions A') - N))%nat by lia.
rewrite seq_app, flat_map_app.
rewrite (flat_map_ext_in (f A') (f A) (seq 0 N) (fun k _ => K k)).
rewrite (flat_map_nil (f A') (seq (0 + N) _)); [rewrite app_nil_r; reflexivity|].
intros k Hk. apply in_seq in Hk. rewrite K. unfold f.
destruct (region_of A k) as [rg|] eqn:E; [|reflexivity]. pose proof (region_of_lt _ _ _ E). unfold N in Hk. lia.
Qed.
Hypothesis NEW_disj : forall p e, newa = [p] -> In e (footprint A) -> ranges_disjoint (ptr_addr L' p, PGSZ) (crange L e).
Hypothesis NEW_range : forall p, newa = [p] -> 0 < ptr_addr L' p /\ ptr_addr L' p + PGSZ < 2 ^ 63.
Hypothesis ALN_new : forall k rg, (N <= k)%nat -> region_of A' k = Some rg -> rg_live rg = true -> ly_reg L' k mod PGSZ = 0.
Hypothesis LIVE_old : forall k rg', (k < N)%nat -> region_of A' k = Some rg' -> rg_live rg' = true ->
exists rg, region_of A k = Some rg /\ rg_live rg = true.
Lemma crange_old : forall e, In e (footprint A) -> crange L' e = crange L e.
Proof.
intros e He. unfold crange. f_equal. apply loc_addr_below.
destruct (In_footprint_inv A e He) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst]; [exact I| |].
- exact (area_prid X R U A HI ar Har).
- cbn. exact (region_of_lt _ _ _ Hr).
Qed.
Theorem layout_ok_xfer : layout_ok L' A'.
Proof using HI MID NA NA1 RGmap RGkeep LEN Lctx Lreg NEW_disj NEW_range ALN_new LIVE_old.
destruct LY as (Y1 & Y2 & Y3 & Y4).
assert (FP' : footprint A' = ((LCtx 0, CTX_SIZE) :: map (fun a => (LMem a, PGSZ)) (st_areas A)) ++ (map (fun a => (LMem a, PGSZ)) newa ++ regions_part A)).
{ rewrite footprint_split, regions_part_same, NA, map_app. cbn [app]. rewrite <- app_assoc. reflexivity. }
assert (FP : footprint A = ((LCtx 0, CTX_SIZE) :: map (fun a => (LMem a, PGSZ)) (st_areas A)) ++ regions_part A) by reflexivity.
assert (OLD : forall e, In e ((LCtx 0, CTX_SIZE) :: map (fun a => (LMem a, PGSZ)) (st_areas A)) \/ In e (regions_part A) -> In e (footprint A)).
{ intros e He. rewrite FP. apply in_app_iff. exact He. }
split; [rewrite Lctx; exact Y1|]. split; [|split].
- intros k rg Hk Hl. destruct (Nat.lt_ge_cases k N) as [HkN | HkN].
+ rewrite (Lreg k HkN). destruct (LIVE_old k rg HkN Hk Hl) as (rg0 & H0 & L0). exact (Y2 k rg0 H0 L0).
+ exact (ALN_new k rg HkN Hk Hl).
- rewrite FP'. rewrite FP in Y3. rewrite map_app in Y3 |- *. apply pairwise_app_inv in Y3 as (P1 & P2 & P3).
rewrite map_app. apply pairwise_app.
+ erewrite map_ext_in; [exact P1|]. intros e He. apply crange_old. apply OLD. left. exact He.
+ apply pairwise_app.
* destruct newa_cases as [En|[p En]]; rewrite En; cbn; [exact I|]. split; [intros ? []| exact I].
* erewrite map_ext_in; [exact P2|]. intros e He. apply crange_old. apply OLD. right. exact He.
* intros x y Hx Hy. destruct newa_cases as [En|[p En]]; rewrite En in Hx; [destruct Hx|]. cbn in Hx. destruct Hx as [<-|[]].
apply in_map_iff in Hy as (e & <- & He). rewrite (crange_old e) by (apply OLD; right; exact He).
unfold crange at 1. cbn [fst snd]. exact (NEW_disj p e En (OLD e (or_intror He))).
+ intros x y Hx Hy. apply in_map_iff in Hx as (e & <- & He). rewrite (crange_old e) by (apply OLD; left; exact He).
apply in_app_iff in Hy as [Hy|Hy].
* destruct newa_cases as [En|[p En]]; rewrite En in Hy; [destruct Hy|]. cbn in Hy. destruct Hy as [<-|[]].
apply ranges_disjoint_sym. unfold crange at 1. cbn [fst snd]. exact (NEW_disj p e En (OLD e (or_introl He))).
* apply in_map_iff in Hy as (e' & <- & He'). rewrite (crange_old e') by (apply OLD; right; exact He').
apply P3; apply in_map; assumption.
- rewrite FP'. intros e He. apply in_app_iff in He as [He|He]; [|apply in_app_iff in He as [He|He]].
+ rewrite (crange_old e) by (apply OLD; left; exact He). apply Y4. apply OLD. left. exact He.
+ destruct newa_cases as [En|[p En]]; rewrite En in He; [destruct He|]. cbn in He. destruct He as [<-|[]].
unfold crange. cbn [fst snd]. exact (NEW_range p En).
+ rewrite (crange_old e) by (apply OLD; right; exact He). apply Y4. apply OLD. right. exact He.
Qed.
End a0.
Lemma statics_xfer : forall B mem mem' (W : Z -> Prop),
syms_ok B -> statics_ok B mem ->
(forall x, 0 <= x < 2 ^ 64 -> ~ W x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
(forall x, static_owned B x -> ~ W x) ->
statics_ok B mem'.
Proof.
intros B mem mem' W SO ST FR NW.
assert (EQ : forall x, static_owned B x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x).
{ intros x Hs. unfold mbyte. rewrite (FR x); [reflexivity | | exact (NW x Hs)].
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hs)). pose proof (proj1 alloc_ceiling_val). lia. }
split.
- rewrite EQ; [apply (st_needlocks _ _ ST) | unfold static_owned; lia].
- intros k Hk. rewrite EQ; [apply (st_pagesize _ _ ST); exact Hk | unfold static_owned; lia].
- intros k Hk. rewrite EQ; [apply (st_lock _ _ ST); exact Hk | unfold static_owned; lia].
- intros k Hk. rewrite EQ; [apply (st_got _ _ ST); exact Hk | unfold static_owned; lia].
- destruct (st_guard _ _ ST) as [g Hg]. exists g. intros k Hk. rewrite EQ; [apply Hg; exact Hk | unfold static_owned; lia].
- intros a Ha. rewrite EQ; [apply (st_tables _ _ ST); exact Ha | unfold static_owned; unfold table_addr in Ha; lia].
Qed.
End h.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
