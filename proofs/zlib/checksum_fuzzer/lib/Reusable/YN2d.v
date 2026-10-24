(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0h YK0i YK15 YM06 YM02 YP09 YK0v YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0x YO0z YO0s YO0u YO0v YO10 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN31 YN2b YN2e YN2c YN2f YN2g.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma loc_addr_LMem' L p : loc_addr L (LMem p) = ly_reg L (prid p) + poff p.
Proof. destruct p; reflexivity. Qed.
Lemma prid_padd' : forall p d, prid (padd p d) = prid p.
Proof. intros [r o] d; reflexivity. Qed.
Lemma poff_padd : forall p d, poff (padd p d) = poff p + d.
Proof. intros [r o] d; reflexivity. Qed.
Lemma reg_lo_le : forall rg, 0 <= reg_lo rg <= PGSZ.
Proof. intros rg. unfold reg_lo, PGSZ. destruct (rg_kind rg); lia. Qed.
Lemma pairwise_app_inv {X} (R : X -> X -> Prop) : forall l1 l2,
pairwise R (l1 ++ l2) -> pairwise R l1 /\ pairwise R l2 /\ (forall x y, In x l1 -> In y l2 -> R x y).
Proof.
induction l1 as [|x l1 IH]; intros l2 H; cbn in *.
- split; [exact I|]. split; [exact H|]. intros ? ? [].
- destruct H as [H1 H2]. destruct (IH l2 H2) as (P1 & P2 & P3). repeat split; auto.
+ intros y Hy. apply H1. apply in_app_iff. left. exact Hy.
+ intros x' y [<-|Hx] Hy; [apply H1; apply in_app_iff; right; exact Hy | apply P3; assumption].
Qed.
Lemma pairwise_remove {X} (R : X -> X -> Prop) : forall l1 x l2,
pairwise R (l1 ++ x :: l2) -> pairwise R (l1 ++ l2).
Proof.
induction l1 as [|y l1 IH]; intros x l2 H; cbn in *.
- exact (proj2 H).
- destruct H as [H1 H2]. split; [| apply (IH x l2 H2)].
intros z Hz. apply H1. apply in_app_iff in Hz as [Hz|Hz]; apply in_app_iff; [left | right; right]; assumption.
Qed.
Lemma with_vmmaps_twice : forall v v' m, with_vmmaps v' (with_vmmaps v m) = with_vmmaps v' m.
Proof. intros v v' [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma munmap_model_with : forall addr n m,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
munmap_model addr n m = with_vmmaps (m_vmmaps (munmap_model addr n m)) m.
Proof.
intros addr n [fd [maps lazy mat] io fs proc lim tm] Hl Hm. unfold m_vm_lazy, m_vm_materialized in *. cbn in *. subst. reflexivity.
Qed.
Lemma munmap_model_no_mat : forall addr n m,
m_vm_materialized m = [] -> m_vm_materialized (munmap_model addr n m) = [].
Proof.
intros addr n m H. unfold munmap_model, with_mmap_destroyed, vm_forget_range, with_vm_backing, with_vmmaps.
cbn [m_vm_materialized]. unfold m_vm_materialized in H |- *. cbn. rewrite H. reflexivity.
Qed.
Lemma munmap_model_maps : forall addr n m,
vm_maps (m_vmmaps (munmap_model addr n m)) = map_remove (vm_maps (m_vmmaps m)) addr /\
vm_noaccess (m_vmmaps (munmap_model addr n m)) = maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) /\
vm_reserved (m_vmmaps (munmap_model addr n m)) = vm_reserved (m_vmmaps m) /\
vm_brk (m_vmmaps (munmap_model addr n m)) = vm_brk (m_vmmaps m) /\
vm_start_brk (m_vmmaps (munmap_model addr n m)) = vm_start_brk (m_vmmaps m) /\
vm_limit (m_vmmaps (munmap_model addr n m)) = vm_limit (m_vmmaps m).
Proof. intros. repeat split; reflexivity. Qed.
Lemma vm_backing_used_le_maps : forall m,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
vm_backing_used m <= State.live_bytes (vm_maps (m_vmmaps m)).
Proof.
intros m Hl Hm. unfold vm_backing_used, vm_backed_maps. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat].
pose proof (maps_subtract_all_le (vm_noaccess (m_vmmaps m)) (vm_maps (m_vmmaps m))). lia.
Qed.
Lemma length_map_remove : forall maps lo n,
In (lo, n) maps -> (length (map_remove maps lo) < length maps)%nat.
Proof.
induction maps as [|[b m] maps IH]; intros lo n Hin; [destruct Hin|].
unfold map_remove in *. cbn [List.filter fst]. destruct Hin as [E|Hin].
- injection E as -> ->. rewrite bv_eqb_refl. cbn [negb].
pose proof (filter_length_le (fun p : word * word => negb (bv_eqb (fst p) lo)) maps). cbn [length]. lia.
- specialize (IH lo n Hin). destruct (negb (bv_eqb b lo)); cbn [length]; lia.
Qed.
Lemma map_contains_subtract : forall l (lo n : word) clo chi,
map_contains l lo n = true -> 0 < bv_unsigned n ->
(bv_unsigned lo + bv_unsigned n <= clo \/ chi <= bv_unsigned lo) -> clo <= chi ->
map_contains (maps_subtract l clo chi) lo n = true.
Proof.
induction l as [|[b m] l IH]; intros lo n clo chi H Hn Hd Hc; [discriminate|].
unfold map_contains in H |- *. cbn [existsb fst snd maps_subtract] in H |- *. rewrite existsb_app.
apply orb_prop in H as [H|H].
- apply orb_true_iff. left. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (u64_range b). pose proof (u64_range m). pose proof (u64_range lo). pose proof (u64_range n).
unfold iv_subtract. cbv zeta. rewrite existsb_app. apply orb_true_iff.
destruct Hd as [Hd|Hd].
+ left. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [existsb fst snd]. rewrite orb_false_r.
apply andb_true_intro. rewrite u64_of_Z by lia. split; apply Z.leb_le; lia.
+ right. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [existsb fst snd]. rewrite orb_false_r.
apply andb_true_intro. rewrite !u64_of_Z by lia. split; apply Z.leb_le; lia.
- apply orb_true_iff. right. apply (IH lo n clo chi H Hn Hd Hc).
Qed.
Section DM.
Variable B : malloc_syms.
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (a : word) (n : Z).
Hypothesis MX : MRx B L A mem md.
Hypothesis Hn : MMAP_THRESHOLD <= n < 2 ^ 62.
Hypothesis GR : grant_ok (Z_to_bv 64 0) md a (dlen n) = true.
Hypothesis ENC : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Hypothesis ENS : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ static_owned B x.
Hypothesis ERRIMG : forall x, errno_addr B <= x < errno_addr B + 4 -> in_img B x.
Hypothesis SNC : forall x, static_owned B x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Variables (L3 : layout) (A3 : astate) (mem6 : word -> option byte) (md3 : Model).
Hypothesis MID3 : midrep B L3 A3 mem6 md3.
Hypothesis LE3 : layout_le (dA2 A n) (L1 L A a) L3.
Hypothesis FR3 : am_frame (dA2 A n) A3.
Hypothesis UB3 : ub_same (dA2 A n) A3.
Variable X3 : list sptr.
Hypothesis HI3 : Inv X3 None U0 A3.
Hypothesis EU3 : forall g am, usedX X3 A3 g am <-> usedX [] A g am.
Hypothesis HX3 : forall g am, memb g X3 = true -> MT A3 g <> Some (MUsed am).
Lemma span_ok_A3 : span_ok A3.
Proof.
intros g am Hg Hlt. destruct (memb g X3) eqn:E.
- exfalso. exact (HX3 g am E Hg).
- assert (HU : usedX X3 A3 g am) by (unfold usedX, MTX; rewrite E; exact Hg).
apply (proj1 (EU3 g am)) in HU. unfold usedX, MTX in HU. cbn [memb] in HU.
exact (MRx_span _ _ _ _ _ MX g am HU Hlt).
Qed.
Let len := dlen n.
Let r0 := r0 A.
Let M : MRc B L A mem md := MRx_MRc _ _ _ _ _ MX.
Let HW : WF A := mc_wf _ _ _ _ _ M.
Let G3 : ledger_ok B L3 A3 md3 := mid_ledger _ _ _ _ _ MID3.
Let Y3 : ledger_x L3 A3 md3 := mid_ledgerx _ _ _ _ _ MID3.
Lemma Hlen : 0 < len /\ len mod PGSZ = 0.
Proof. exact (dlen_pos n (proj1 Hn)). Qed.
Lemma aZ : 0 <= bv_unsigned a < 2 ^ 64.
Proof. apply u64_range. Qed.
Lemma L3_r0 : ly_reg L3 r0 = bv_unsigned a.
Proof.
destruct LE3 as (_ & _ & _ & E). rewrite (E r0).
- apply L1_new.
- pose proof (dA2_fields A n) as (_&_&_&_&_&_&_&ER&_). rewrite ER, length_app. cbn. unfold r0, YN2c.r0. lia.
Qed.
Lemma L3_old : forall k, (k < r0)%nat -> ly_reg L3 k = ly_reg L k.
Proof.
intros k Hk. destruct LE3 as (_ & _ & _ & E). rewrite (E k).
- apply (proj2 (proj2 (proj2 (layout_le_L1 L A a len (dlen_pos n (proj1 Hn)))))). exact Hk.
- pose proof (dA2_fields A n) as (_&_&_&_&_&_&_&ER&_). rewrite ER, length_app. cbn. unfold r0, YN2c.r0 in Hk. lia.
Qed.
Lemma L3_ctx : ly_ctx L3 = ms_ctx B.
Proof. exact (mid_ctx _ _ _ _ _ MID3). Qed.
Lemma A3_r0 : region_of A3 r0 = Some (rgn len).
Proof. exact (A3_region A n A3 (proj1 Hn) FR3). Qed.
Lemma r0_placed : bv_unsigned a mod PGSZ = 0 /\ 4096 <= bv_unsigned a /\ bv_unsigned a + len <= alloc_ceiling /\
(forall x, bv_unsigned a <= x < bv_unsigned a + len -> ~ in_img B x).
Proof. pose proof (lg_placed _ _ _ _ G3 r0 (rgn len) A3_r0 eq_refl) as H. rewrite L3_r0 in H. exact H. Qed.
Lemma old_region_A3 : forall k rg, region_of A k = Some rg -> rg_kind rg = RkMap -> region_of A3 k = Some rg.
Proof.
intros k rg Hk Hkind. destruct FR3 as (_ & _ & Hr & _). apply Hr; [|exact Hkind].
unfold dA2. rewrite (region_of_A2 A (dlen n) (dlen_pos n (proj1 Hn))).
unfold YN2c.r0. rewrite (proj2 (Nat.ltb_lt _ _) (region_of_lt A k rg Hk)). exact Hk.
Qed.
Lemma used_metas_A3 : used_metas A3 = used_metas A.
Proof. exact (A3_used_metas A n A3 UB3 X3 HI3 HX3 EU3). Qed.
Lemma tail_cells_A3 : tail_cells A3 = tail_cells A.
Proof. unfold tail_cells. rewrite used_metas_A3. reflexivity. Qed.
Lemma user_blocks_A3 : user_blocks A3 = user_blocks A.
Proof. unfold user_blocks. rewrite used_metas_A3. reflexivity. Qed.
Lemma frames_A3 : frames A3 = frames A.
Proof. unfold frames. rewrite used_metas_A3. reflexivity. Qed.
Lemma disjoint_r0 : forall k rg x, k <> r0 -> region_of A3 k = Some rg -> rg_live rg = true ->
ly_reg L3 k + reg_lo rg <= x < ly_reg L3 k + rg_len rg -> ~ (bv_unsigned a <= x < bv_unsigned a + len).
Proof.
intros k rg x Hk Hr Hl Hx Hin. pose proof Hlen as [P _].
pose proof (lx_regs _ _ _ Y3 k r0 rg (rgn len) Hk Hr A3_r0 Hl eq_refl ltac:(lia) ltac:(cbn; lia)) as D.
unfold ranges_disjoint in D. cbn [fst snd reg_lo rgn rg_kind rg_len] in D. rewrite L3_r0 in D. lia.
Qed.
Definition cell_home_ok (x : Z) : Prop :=
4096 <= x < alloc_ceiling /\ (in_img B x -> ms_ctx B <= x < ms_ctx B + CTX_SIZE) /\
~ (errno_addr B <= x < errno_addr B + 4) /\ ~ (bv_unsigned a <= x < bv_unsigned a + len).
Lemma region_byte_ok : forall k rg x, k <> r0 -> region_of A3 k = Some rg -> rg_live rg = true ->
ly_reg L3 k + reg_lo rg <= x < ly_reg L3 k + rg_len rg -> cell_home_ok x.
Proof.
intros k rg x Hk Hr Hl Hx. pose proof (lg_placed _ _ _ _ G3 k rg Hr Hl) as (_ & Hlo & Hhi & Himg). pose proof (reg_lo_le rg).
split; [lia|]. split; [intros Hi; exfalso; apply (Himg x); [lia | exact Hi]|]. split.
- intros He. apply (Himg x); [lia|]. apply ERRIMG. exact He.
- apply (disjoint_r0 k rg x Hk Hr Hl Hx).
Qed.
Lemma ctx_byte_ok : forall x, ms_ctx B <= x < ms_ctx B + CTX_SIZE -> cell_home_ok x.
Proof.
intros x Hx. pose proof (mid_syms _ _ _ _ _ MID3) as SO.
pose proof (so_ctx_lo _ SO). pose proof (so_ctx_hi _ SO).
split; [lia|]. split; [auto|]. split.
- intros He. exact (ENC x He Hx).
- intros Hin. apply (proj2 (proj2 (proj2 r0_placed)) x Hin). apply (so_ctx_img _ SO). exact Hx.
Qed.
Lemma cells_A3_home : forall c j, In c (image A3) \/ In c (tail_cells A3) -> (j < mc_w c)%nat ->
cell_home_ok (loc_addr L3 (mc_loc c) + Z.of_nat j).
Proof.
intros c j Hc Hj. destruct Hc as [Hc | Hc].
- unfold image in Hc. rewrite !in_app_iff in Hc. destruct Hc as [Hc | [Hc | Hc]].
+   destruct (In_ctx_cells A3 c Hc) as (off & E & Ho & Hw). rewrite E. cbn [loc_addr]. rewrite L3_ctx.
apply ctx_byte_ok. lia.
+   apply In_areas_cells in Hc as (ar & next & Har & Hc).
destruct (In_area_cells A3 ar next c Hc) as (d & E & Hd & Hw). rewrite E.
destruct (inv_areas HI3) as (_ & Hareas & _). destruct (Hareas ar Har) as (k & o & rg & -> & _ & Ho & Hr & Hl & Hsz & Hkind).
rewrite loc_addr_LMem', prid_padd', poff_padd. cbn [prid poff].
assert (Hk : k <> r0) by (intros ->; rewrite A3_r0 in Hr; injection Hr as <-; exact Hkind).
apply (region_byte_ok k rg _ Hk Hr Hl). pose proof (reg_lo_le rg). lia.
+   apply in_flat_map in Hc as ([g am] & Hg & Hc). cbn [fst snd] in Hc. rewrite used_metas_A3 in Hg.
apply (used_metas_usedX A g am HW) in Hg.
destruct (used_group_region [] None U0 A g am HW Hg) as (rg & Hr & Hkind & Hl & Ho & Hext & _).
destruct (In_group_cells [] None U0 A g am c HW Hg Hc) as (d & E & Hd & Hw). rewrite E.
rewrite loc_addr_LMem', prid_padd', poff_padd.
pose proof (fresh A HW g am Hg) as Hlt. pose proof (old_region_A3 _ _ Hr Hkind) as Hr3.
apply (region_byte_ok (prid (am_mem am)) rg _ ltac:(unfold r0; lia) Hr3 Hl). unfold reg_lo. rewrite Hkind. lia.
- rewrite tail_cells_A3 in Hc. destruct (tail_cell_region A HW c Hc) as (p & rg & E & Hr & Hkind & Hl & Ho & Hw).
rewrite E, loc_addr_LMem'. pose proof (region_of_lt A _ _ Hr) as Hlt. pose proof (old_region_A3 _ _ Hr Hkind) as Hr3.
apply (region_byte_ok (prid p) rg _ ltac:(unfold r0, YN2c.r0; lia) Hr3 Hl). unfold reg_lo. rewrite Hkind. lia.
Qed.
Definition r0_entry : loc * Z := (LMem (SP r0 0), len).
Lemma footprint_A3_home : forall e x, In e (footprint A3) -> e <> r0_entry ->
loc_addr L3 (fst e) <= x < loc_addr L3 (fst e) + snd e ->
(fst e = LCtx 0 /\ ms_ctx B <= x < ms_ctx B + CTX_SIZE) \/
(exists p, fst e = LMem p /\ cell_home_ok x /\ ~ in_img B x).
Proof.
intros e x He Hne Hx.
destruct (In_footprint_inv A3 e He) as [-> | [(ar & Har & ->) | (k & rg & Hr & Hkind & Hl & ->)]]; cbn [fst snd loc_addr] in Hx |- *.
- left. rewrite L3_ctx in Hx. split; [reflexivity | lia].
- right. exists ar. split; [reflexivity|].
destruct (inv_areas HI3) as (_ & Hareas & _). destruct (Hareas ar Har) as (k & o & rg & -> & _ & Ho & Hr & Hl & Hsz & Hkind).
cbn [prid poff loc_addr] in Hx.
assert (Hk : k <> r0) by (intros ->; rewrite A3_r0 in Hr; injection Hr as <-; exact Hkind).
pose proof (reg_lo_le rg).
pose proof (region_byte_ok k rg x Hk Hr Hl ltac:(lia)) as OK. split; [exact OK|].
pose proof (lg_placed _ _ _ _ G3 k rg Hr Hl) as (_ & _ & _ & Himg). apply Himg. lia.
- right. exists (SP k 0). split; [reflexivity|].
assert (Hk : k <> r0) by (intros ->; apply Hne; unfold r0_entry; rewrite A3_r0 in Hr; injection Hr as <-; reflexivity).
pose proof (region_byte_ok k rg x Hk Hr Hl ltac:(unfold reg_lo; rewrite Hkind; cbn; lia)) as OK. split; [exact OK|].
pose proof (lg_placed _ _ _ _ G3 k rg Hr Hl) as (_ & _ & _ & Himg). apply Himg. lia.
Qed.
Lemma r0_entry_in : In r0_entry (footprint A3).
Proof. unfold r0_entry. change len with (rg_len (rgn len)). apply footprint_region_In; [exact A3_r0 | reflexivity | reflexivity]. Qed.
Lemma cell_mem_ext : forall Lx m m' c,
(forall j, (j < mc_w c)%nat -> m' (Z_to_bv 64 (loc_addr Lx (mc_loc c) + Z.of_nat j)) = m (Z_to_bv 64 (loc_addr Lx (mc_loc c) + Z.of_nat j))) ->
cell_mem B Lx m c -> cell_mem B Lx m' c.
Proof.
intros Lx m m' [l w v] Heq H. unfold cell_mem in *. cbn [mc_loc mc_w mc_val] in *.
destruct v as [z|p|z|].
1,2,4: intros j Hj; unfold mbyte; rewrite (Heq j Hj); apply H; exact Hj.
intros Hw. destruct (H Hw) as (b & Hb & Hz). exists b. split; [|exact Hz].
unfold mbyte in *. specialize (Heq 0%nat Hw). rewrite Z.add_0_r in Heq. rewrite Heq. exact Hb.
Qed.
Lemma statics_ok_ext : forall m m',
(forall x, static_owned B x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) -> statics_ok B m -> statics_ok B m'.
Proof.
intros m m' Heq ST.
assert (SO : forall x, static_owned B x -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x).
{ intros x Hx. unfold mbyte. rewrite (Heq x Hx). reflexivity. }
split.
- rewrite SO; [apply (st_needlocks _ _ ST) | unfold static_owned; lia].
- intros k Hk. rewrite SO; [apply (st_pagesize _ _ ST); exact Hk | unfold static_owned; lia].
- intros k Hk. rewrite SO; [apply (st_lock _ _ ST); exact Hk | unfold static_owned; lia].
- intros k Hk. rewrite SO; [apply (st_got _ _ ST); exact Hk | unfold static_owned; lia].
- destruct (st_guard _ _ ST) as [g Hg]. exists g. intros k Hk. rewrite SO; [apply Hg; exact Hk | unfold static_owned; lia].
- intros x Hx. rewrite SO; [apply (st_tables _ _ ST); exact Hx | unfold static_owned; unfold table_addr in Hx; lia].
Qed.
Lemma static_byte_ok : forall x, static_owned B x ->
0 <= x < alloc_ceiling /\ ~ (errno_addr B <= x < errno_addr B + 4) /\ ~ (bv_unsigned a <= x < bv_unsigned a + len).
Proof.
intros x Hs. pose proof (mid_syms _ _ _ _ _ MID3) as SO.
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hs)). split; [lia|]. split.
- intros He. exact (ENS x He Hs).
- intros Hin. apply (proj2 (proj2 (proj2 r0_placed)) x Hin). apply (so_statics_img _ SO). exact Hs.
Qed.
Lemma footprint_split : forall A',
st_areas A' = st_areas A3 -> length (st_regions A') = length (st_regions A3) ->
(forall k, k <> r0 -> region_of A' k = region_of A3 k) ->
region_of A' r0 = Some (YO0i.mkRegion RkMap len [] false) \/ region_of A' r0 = region_of A3 r0 ->
exists l1 l2, footprint A3 = l1 ++ r0_entry :: l2 /\
footprint A' = l1 ++ (if region_of A' r0 then (match region_of A' r0 with Some rg => if rg_live rg then [r0_entry] else [] | None => [] end) else []) ++ l2.
Proof.
intros A' Ea El Er Hr0.
pose proof (region_of_lt A3 r0 _ A3_r0) as Hlt.
set (F := fun s k => match region_of s k with
| Some rg => match rg_kind rg with RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else [] | _ => [] end
| None => [] end).
assert (EF : forall s, footprint s = (LCtx 0, CTX_SIZE) :: map (fun ar => (LMem ar, PGSZ)) (st_areas s) ++ flat_map (F s) (seq 0 (length (st_regions s)))) by reflexivity.
assert (ES : seq 0 (length (st_regions A3)) = seq 0 r0 ++ r0 :: seq (S r0) (length (st_regions A3) - S r0)).
{ replace (length (st_regions A3)) with (r0 + S (length (st_regions A3) - S r0))%nat at 1 by lia.
rewrite seq_app. reflexivity. }
exists ((LCtx 0, CTX_SIZE) :: map (fun ar => (LMem ar, PGSZ)) (st_areas A3) ++ flat_map (F A3) (seq 0 r0)),
(flat_map (F A3) (seq (S r0) (length (st_regions A3) - S r0))).
assert (FR0 : F A3 r0 = [r0_entry]) by (unfold F; rewrite A3_r0; reflexivity).
split.
- rewrite (EF A3), ES, flat_map_app.
change (flat_map (F A3) (r0 :: ?sq)) with (F A3 r0 ++ flat_map (F A3) sq). rewrite FR0.
cbn [app]. rewrite app_assoc. reflexivity.
- rewrite (EF A'), Ea, El, ES, flat_map_app.
change (flat_map (F A') (r0 :: ?sq)) with (F A' r0 ++ flat_map (F A') sq).
rewrite (flat_map_ext_in (F A') (F A3) (seq 0 r0)) by (intros k Hk; apply in_seq in Hk; unfold F; rewrite Er by lia; reflexivity).
rewrite (flat_map_ext_in (F A') (F A3) (seq (S r0) _)) by (intros k Hk; apply in_seq in Hk; unfold F; rewrite Er by lia; reflexivity).
replace (F A' r0) with (if region_of A' r0 then match region_of A' r0 with Some rg => if rg_live rg then [r0_entry] else [] | None => [] end else []).
+ cbn [app]. rewrite app_assoc. reflexivity.
+ unfold F. destruct Hr0 as [E|E]; rewrite E; [reflexivity|]. rewrite A3_r0. reflexivity.
Qed.
Lemma footprint_A3_disjoint : forall l1 l2 e x, footprint A3 = l1 ++ r0_entry :: l2 -> In e (l1 ++ l2) ->
loc_addr L3 (fst e) <= x < loc_addr L3 (fst e) + snd e -> ~ (bv_unsigned a <= x < bv_unsigned a + len) /\ e <> r0_entry.
Proof.
intros l1 l2 e x Hfp He Hx. pose proof Hlen as [P _].
pose proof (mid_layout _ _ _ _ _ MID3) as (_ & _ & Y3p & _). rewrite Hfp, map_app in Y3p. cbn [map] in Y3p.
apply pairwise_app_inv in Y3p as (_ & [Q1 Q2] & Q3).
assert (CR : crange L3 r0_entry = (bv_unsigned a, len)) by (unfold crange, r0_entry; cbn [fst snd loc_addr]; rewrite L3_r0, Z.add_0_r; reflexivity).
assert (D : ranges_disjoint (crange L3 e) (crange L3 r0_entry)).
{ apply in_app_iff in He as [He|He].
- apply Q3; [apply in_map; exact He | left; reflexivity].
- apply ranges_disjoint_sym. apply Q1. apply in_map. exact He. }
rewrite CR in D. unfold ranges_disjoint, crange in D. cbn [fst snd] in D. split; [lia|].
intros ->. unfold r0_entry in Hx, D. cbn [fst snd loc_addr] in Hx, D. rewrite L3_r0 in Hx, D. lia.
Qed.
Section D2.
Hypothesis X3nil : X3 = [].
Variable sp : Z.
Hypothesis Hsp : alloc_ceiling + ALLOC_STACK <= sp.
Variable mem8 : word -> option byte.
Hypothesis AG8 : forall x, 0 <= x < 2 ^ 64 ->
~ ((sp - ALLOC_STACK <= x < sp) \/ (errno_addr B <= x < errno_addr B + 4)) ->
~ (bv_unsigned a <= x < bv_unsigned a + len) -> mem8 (Z_to_bv 64 x) = mem6 (Z_to_bv 64 x).
Let A4 := dm_kill A A3.
Let md4 := munmap_model a (Z_to_bv 64 len) md3.
Let HI3n : Inv [] None U0 A3.
Proof. rewrite <- X3nil. exact HI3. Qed.
Let EU3n : forall g am, usedX [] A3 g am <-> usedX [] A g am.
Proof. intros g am. rewrite <- (EU3 g am), X3nil. tauto. Qed.
Lemma kept : forall x, cell_home_ok x -> mem8 (Z_to_bv 64 x) = mem6 (Z_to_bv 64 x).
Proof.
intros x (H1 & H2 & H3 & H4). pose proof (proj1 alloc_ceiling_val). apply AG8; [lia | | exact H4].
intros [Hs|He]; [unfold ALLOC_STACK in *; lia | exact (H3 He)].
Qed.
Lemma A4_region_of : forall k, region_of A4 k = if Nat.eqb k r0 then Some (YO0i.mkRegion RkMap len [] false) else region_of A3 k.
Proof. intros k. exact (kill_region_of A n A3 (proj1 Hn) FR3 k). Qed.
Lemma A4_fields : st_metas A4 = st_metas A3 /\ st_areas A4 = st_areas A3 /\ st_usage A4 = st_usage A3 /\
st_meta_alloc_shift A4 = st_meta_alloc_shift A3 /\ st_avail_meta_areas A4 = st_avail_meta_areas A3 /\
length (st_regions A4) = length (st_regions A3) /\ st_brk A4 = st_brk A3 /\ st_init_done A4 = st_init_done A3 /\
st_mmap_counter A4 = st_mmap_counter A3 /\ st_seq A4 = st_seq A3 /\ st_unmap_seq A4 = st_unmap_seq A3.
Proof. exact (kill_fields A A3). Qed.
Lemma A4_footprint : exists l1 l2, footprint A3 = l1 ++ r0_entry :: l2 /\ footprint A4 = l1 ++ l2.
Proof.
pose proof A4_fields as (E1 & E2 & _ & _ & _ & E6 & _).
destruct (footprint_split A4 E2 E6) as (l1 & l2 & H3 & H4).
- intros k Hk. rewrite A4_region_of. rewrite (proj2 (Nat.eqb_neq _ _) Hk). reflexivity.
- left. rewrite A4_region_of, Nat.eqb_refl. reflexivity.
- exists l1, l2. split; [exact H3|]. rewrite H4, A4_region_of, Nat.eqb_refl. reflexivity.
Qed.
Lemma memrep_A4 : memrep B L3 A4 mem8.
Proof.
pose proof (mid_mem _ _ _ _ _ MID3) as (C1 & C2 & C3).
assert (CELL : forall c, In c (image A3) \/ In c (tail_cells A3) -> cell_mem B L3 mem6 c -> cell_mem B L3 mem8 c).
{ intros c Hc H. eapply cell_mem_ext; [|exact H]. intros j Hj. apply kept. apply cells_A3_home; assumption. }
split; [|split].
- unfold A4. rewrite (kill_image A n A3 FR3 UB3 HI3n EU3n). apply Forall_forall. intros c Hc. apply CELL; [left; exact Hc|].
exact (proj1 (Forall_forall _ _) C1 c Hc).
- replace (tail_cells A4) with (tail_cells A3) by (unfold tail_cells, used_metas; rewrite (proj1 A4_fields); reflexivity).
apply Forall_forall. intros c Hc. apply CELL; [right; exact Hc|]. exact (proj1 (Forall_forall _ _) C2 c Hc).
- destruct A4_footprint as (l1 & l2 & F3 & F4). rewrite F4. apply Forall_forall. intros e He.
assert (He3 : In e (footprint A3)) by (rewrite F3; apply in_app_iff in He as [He|He]; apply in_app_iff; [left | right; right]; exact He).
pose proof (proj1 (Forall_forall _ _) C3 e He3) as F. unfold foot_ok in *. destruct (fst e) as [o|p] eqn:Efst; [exact I|].
intros x Hx. destruct (F x Hx) as [b Hb]. exists b.
destruct (footprint_A3_disjoint l1 l2 e x F3 He ltac:(rewrite Efst; exact Hx)) as [Hout Hne].
destruct (footprint_A3_home e x He3 Hne ltac:(rewrite Efst; exact Hx)) as [[E _] | (p' & _ & OK & _)]; [congruence|].
rewrite (kept x OK). exact Hb.
Qed.
Lemma tail_geom_A4 : tail_geom L3 A4.
Proof.
unfold tail_geom. replace (tail_cells A4) with (tail_cells A3) by (unfold tail_cells, used_metas; rewrite (proj1 A4_fields); reflexivity).
apply Forall_forall. intros c Hc j Hj.
pose proof (proj1 (Forall_forall _ _) (mid_tailg _ _ _ _ _ MID3) c Hc j Hj) as [(e & He & Hx) Hnb].
destruct A4_footprint as (l1 & l2 & F3 & F4).
pose proof (cells_A3_home c j (or_intror Hc) Hj) as OK. destruct OK as (_ & _ & _ & Hout).
split.
- exists e. split; [|exact Hx]. rewrite F4. rewrite F3 in He. apply in_app_iff in He as [He|[<-|He]]; [apply in_app_iff; left; exact He | | apply in_app_iff; right; exact He].
exfalso. unfold r0_entry in Hx. cbn [fst snd loc_addr] in Hx. rewrite L3_r0 in Hx. lia.
- intros (b & Hb & Hbx). apply Hnb. exists b. split; [|exact Hbx].
unfold user_blocks, used_metas in Hb |- *. rewrite (proj1 A4_fields) in Hb. exact Hb.
Qed.
Lemma statics_A4 : statics_ok B mem8.
Proof.
apply (statics_ok_ext mem6); [| exact (mid_statics _ _ _ _ _ MID3)].
intros x Hs. destruct (static_byte_ok x Hs) as (H1 & H2 & H3). pose proof (proj1 alloc_ceiling_val).
apply AG8; [lia | | exact H3]. intros [Hs'|He]; [unfold ALLOC_STACK in *; lia | exact (H2 He)].
Qed.
Lemma layout_ok_A4 : layout_ok L3 A4.
Proof.
pose proof (mid_layout _ _ _ _ _ MID3) as (Y1 & Y2 & Y3p & Y4).
destruct A4_footprint as (l1 & l2 & F3 & F4).
split; [exact Y1|]. split; [|split].
- intros k rg Hk Hl. rewrite A4_region_of in Hk. destruct (Nat.eqb_spec k r0); [injection Hk as <-; discriminate | exact (Y2 k rg Hk Hl)].
- rewrite F4, map_app. rewrite F3, map_app in Y3p. cbn [map] in Y3p. exact (pairwise_remove _ _ _ _ Y3p).
- intros e He. apply Y4. rewrite F3. rewrite F4 in He. apply in_app_iff in He as [He|He]; apply in_app_iff; [left | right; right]; exact He.
Qed.
Lemma r0_maps_entry : In (a, Z_to_bv 64 len) (vm_maps (m_vmmaps md3)).
Proof.
pose proof (lg_maps _ _ _ _ G3 r0 (rgn len) A3_r0 eq_refl ltac:(discriminate)) as H.
unfold w64 in H. rewrite L3_r0, Z_to_bv_bv_unsigned in H. exact H.
Qed.
Lemma len_u : bv_unsigned (Z_to_bv 64 len) = len.
Proof. pose proof r0_placed as (_ & _ & Hc & _). pose proof (proj1 alloc_ceiling_val). pose proof Hlen. pose proof aZ. apply u64_of_Z. lia. Qed.
Lemma entry_not_at_a : forall e, In e (vm_maps (m_vmmaps md3)) -> e <> (a, Z_to_bv 64 len) -> fst e <> a.
Proof.
intros e He Hne E. destruct (lx_disj _ _ _ Y3 e _ He r0_maps_entry) as [H|H]; [exact (Hne H)|].
destruct (lx_maps _ _ _ Y3 e He) as [P _]. pose proof Hlen as [P2 _].
unfold ranges_disjoint, iv_lo, iv_len in H, P. cbn [fst snd] in H. rewrite E, len_u in H. lia.
Qed.
Lemma entry_in_r0 : forall e, In e (vm_maps (m_vmmaps md3)) ->
bv_unsigned a <= iv_lo e -> iv_lo e + iv_len e <= bv_unsigned a + len -> e = (a, Z_to_bv 64 len).
Proof.
intros e He H1 H2. destruct (lx_disj _ _ _ Y3 e _ He r0_maps_entry) as [H|H]; [exact H|].
destruct (lx_maps _ _ _ Y3 e He) as [P _]. exfalso.
unfold ranges_disjoint, iv_lo, iv_len in *. cbn [fst snd] in H. rewrite len_u in H. lia.
Qed.
Lemma ledger_ok_A4 : ledger_ok B L3 A4 md4.
Proof.
pose proof (munmap_model_maps a (Z_to_bv 64 len) md3) as (VM & VN & VR & VB & VS & VL).
pose proof r0_placed as (Ral & Rlo & Rhi & Rimg). pose proof Hlen as [P Pm]. pose proof (proj1 alloc_ceiling_val) as AC. pose proof aZ.
pose proof A4_fields as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _).
assert (PG : PGSZ = 4096) by reflexivity.
split; unfold md4; rewrite ?VM, ?VN, ?VR, ?VB, ?VS, ?VL.
- exact (lg_reserved _ _ _ _ G3).
- exact (lg_limit _ _ _ _ G3).
- intros k rg Hk Hl Hkind. rewrite A4_region_of in Hk. destruct (Nat.eqb_spec k r0) as [->|Hne]; [injection Hk as <-; discriminate|].
pose proof (lg_maps _ _ _ _ G3 k rg Hk Hl Hkind) as Hin. apply In_map_remove. split; [exact Hin|].
apply (entry_not_at_a _ Hin). intros E.
pose proof (lg_placed _ _ _ _ G3 k rg Hk Hl) as (_ & Klo & Khi & _).
destruct (inv_areas HI3) as (_&_&_&_&_&_&_&_&A9). pose proof (A9 k rg Hk).
assert (Ek : ly_reg L3 k = bv_unsigned a /\ rg_len rg = len).
{ pose proof (f_equal (fun p => bv_unsigned (fst p)) E) as E1'. pose proof (f_equal (fun p => bv_unsigned (snd p)) E) as E2'.
cbn [fst snd] in E1', E2'. unfold w64 in *. rewrite u64_of_Z in E1' by lia. rewrite len_u in E2'. rewrite u64_of_Z in E2' by lia. auto. }
destruct Ek as [Ek1 Ek2]. pose proof (reg_lo_le rg). pose proof (dlen_facts n (proj1 Hn)) as (_&_&_&_&D5). fold len in D5.
apply (disjoint_r0 k rg (bv_unsigned a + PGSZ) Hne Hk Hl); unfold PGSZ in *; lia.
- intros k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw. rewrite A4_region_of in Hk. destruct (Nat.eqb_spec k r0) as [->|Hne]; [injection Hk as <-; discriminate|].
destruct (lg_noaccess _ _ _ _ G3 k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw) as [N1 N2].
assert (Hd : ly_reg L3 k + off + PGSZ <= bv_unsigned a \/ bv_unsigned a + len <= ly_reg L3 k + off).
{ pose proof (disjoint_r0 k rg (ly_reg L3 k + off) Hne Hk Hl ltac:(unfold reg_lo; rewrite Hkind; cbn; unfold PGSZ in *; lia)).
pose proof (disjoint_r0 k rg (ly_reg L3 k + off + PGSZ - 1) Hne Hk Hl ltac:(unfold reg_lo; rewrite Hkind; cbn; unfold PGSZ in *; lia)).
destruct (Z_lt_le_dec (ly_reg L3 k + off) (bv_unsigned a)); [left | right]; unfold PGSZ in *; lia. }
pose proof (lg_placed _ _ _ _ G3 k rg Hk Hl) as (_ & Klo & Khi & _).
assert (Upg : bv_unsigned (w64 PGSZ) = PGSZ) by reflexivity.
assert (Ulo : bv_unsigned (w64 (ly_reg L3 k + off)) = ly_reg L3 k + off).
{
pose proof (proj1 alloc_ceiling_val) as ACr. unfold PGSZ in Ho2. clear -Klo Khi Ho1 Ho2 ACr. unfold w64. apply u64_of_Z. lia. }
split.
+ apply map_contains_subtract; [exact N1 | rewrite Upg; unfold PGSZ; lia | rewrite Ulo, Upg, len_u; lia | rewrite len_u; lia].
+ unfold map_contains in N2 |- *. apply existsb_exists in N2 as (e & He & Hc). apply existsb_exists. exists e. split; [|exact Hc].
apply In_map_remove. split; [exact He|]. apply (entry_not_at_a e He). intros ->.
apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. cbn [fst snd] in C1, C2. rewrite Ulo, Upg, len_u in *. unfold PGSZ in *. lia.
- exact (lg_brk0 _ _ _ _ G3).
- rewrite E7. pose proof (lg_brk _ _ _ _ G3) as HB. destruct (st_brk A3); exact HB.
- intros k rg Hk Hl. rewrite A4_region_of in Hk. destruct (Nat.eqb_spec k r0) as [->|Hne]; [injection Hk as <-; discriminate|].
exact (lg_placed _ _ _ _ G3 k rg Hk Hl).
- pose proof (length_map_remove _ _ _ r0_maps_entry). pose proof (lg_count _ _ _ _ G3).
unfold A4. rewrite (kill_nslots A n A3 (proj1 Hn) FR3). lia.
- unfold A4. rewrite (kill_live_bytes A n A3 (proj1 Hn) FR3). apply Forall_forall. intros e He. apply In_map_remove in He as [He Hne].
destruct (lx_in _ _ _ Y3 e He) as (k & rg & Hk & Hl & G1 & G2).
destruct (Nat.eq_dec k r0) as [->|Hk0].
+ rewrite A3_r0 in Hk. injection Hk as <-. cbn [rgn rg_len] in G2. rewrite L3_r0 in G1, G2.
exfalso. apply Hne. rewrite (entry_in_r0 e He G1 G2). reflexivity.
+
assert (Hk4 : region_of (dm_kill A A3) k = Some rg).
{ rewrite (kill_region_of A n A3 (proj1 Hn) FR3). unfold r0 in Hk0. destruct (Nat.eqb_spec k (YN2c.r0 A)); [lia | exact Hk]. }
assert (NN : forall k' rg', region_of (dm_kill A A3) k' = Some rg' -> 0 <= rg_len rg').
{ intros k' rg' Hk'. rewrite (kill_region_of A n A3 (proj1 Hn) FR3) in Hk'.
destruct (Nat.eqb k' (YN2c.r0 A)); [injection Hk' as <-; cbn; lia|].
destruct (inv_areas HI3) as (_&_&_&_&_&_&_&_&A9). exact (A9 k' rg' Hk'). }
pose proof (region_len_le_live len Hlen (dm_kill A A3) k rg NN Hk4 Hl) as LE.
rewrite (kill_live_bytes A n A3 (proj1 Hn) FR3) in LE. unfold iv_lo, iv_len in G1, G2. cbn beta. lia.
- pose proof (lx_lb _ _ _ Y3) as LB. pose proof (live_bytes_map_remove _ _ _ r0_maps_entry) as LR. rewrite len_u in LR.
unfold A4. rewrite (kill_live_bytes A n A3 (proj1 Hn) FR3).
destruct (mid_md _ _ _ _ _ MID3) as (_ & Hlz & Hmat).
pose proof (vm_backing_used_le_maps (munmap_model a (Z_to_bv 64 len) md3) (munmap_model_no_lazy _ _ _ Hlz) (munmap_model_no_mat _ _ _ Hmat)) as VBU.
rewrite VM in VBU. lia.
-   exact (lg_ceil _ _ _ _ G3).
Qed.
Lemma ledger_x_A4 : ledger_x L3 A4 md4.
Proof.
pose proof r0_placed as (Ral & Rlo & Rhi & Rimg). pose proof Hlen as [P Pm]. pose proof (proj1 alloc_ceiling_val) as AC. pose proof aZ as Ha.
pose proof (ledger_x_munmap L3 A3 A4 md3 r0 (rgn len) Y3 A3_r0 eq_refl eq_refl) as LXM.
unfold w64 in LXM. cbn [rg_len rgn] in LXM. rewrite L3_r0, Z_to_bv_bv_unsigned in LXM.
apply LXM; [exact r0_maps_entry | lia | lia | lia |]. intros k. apply A4_region_of.
Qed.
Lemma midrep_A4 : midrep B L3 A4 mem8 md4.
Proof.
destruct (mid_md _ _ _ _ _ MID3) as (H1 & H2 & H3).
split.
- exact (mid_syms _ _ _ _ _ MID3).
- exact memrep_A4.
- exact tail_geom_A4.
- exact statics_A4.
- exact ledger_ok_A4.
- exact ledger_x_A4.
- exact layout_ok_A4.
- exact (mid_ctx _ _ _ _ _ MID3).
- exact (mid_sec _ _ _ _ _ MID3).
- unfold md4. rewrite munmap_model_halted. split; [exact H1|]. split; [apply munmap_model_no_lazy; exact H2 | apply munmap_model_no_mat; exact H3].
Qed.
Theorem MRx_A4 : bounded A3 -> ama_ok A3 -> MRx B L3 A4 mem8 md4.
Proof.
intros HB HA. apply midrep_MRx.
- exact midrep_A4.
- exact (kill_inv A n A3 HW (proj1 Hn) FR3 HI3n EU3n).
- exact (kill_bounded A A3 HB).
- apply (rsv_ok_sub A); [exact (MRx_rsv _ _ _ _ _ MX)|]. intros f Hf. unfold frames, used_metas in Hf |- *.
rewrite (proj1 A4_fields) in Hf. fold (used_metas A3) in Hf. fold (frames A3) in Hf. rewrite frames_A3 in Hf. exact Hf.
- exact (kill_ama A A3 HA).
-
apply (span_ok_same_metas A3); [| exact (proj1 A4_fields)]. exact span_ok_A3.
Qed.
Lemma user_blocks_A4 : user_blocks A4 = user_blocks A.
Proof. unfold user_blocks, used_metas. rewrite (proj1 A4_fields). fold (used_metas A3). fold (user_blocks A3). apply user_blocks_A3. Qed.
Hypothesis VM3 : exists vm3, md3 = with_vmmaps vm3 (md1 md a len).
Lemma md4_with : exists vm', md4 = with_vmmaps vm' md.
Proof.
destruct (mid_md _ _ _ _ _ MID3) as (H1 & H2 & H3). destruct VM3 as [vm3 E3].
exists (m_vmmaps md4). unfold md4 at 1. rewrite (munmap_model_with a (Z_to_bv 64 len) md3 H2 H3).
rewrite E3 at 2. unfold md1, mmap_model. rewrite !with_vmmaps_twice. reflexivity.
Qed.
End D2.
Lemma pairwise_map_In' {X Y} (R : Y -> Y -> Prop) (f : X -> Y) : forall l x y,
pairwise R (map f l) -> In x l -> In y l -> x = y \/ R (f x) (f y) \/ R (f y) (f x).
Proof.
induction l as [|h t IH]; intros x y HP Hx Hy; [destruct Hx|]. cbn in HP. destruct HP as [H1 H2].
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- left. reflexivity.
- right. left. apply H1. apply in_map. exact Hy.
- right. right. apply H1. apply in_map. exact Hx.
- apply IH; assumption.
Qed.
Lemma ledger_ok_same : forall Lx A1 A2 mdx, ledger_ok B Lx A1 mdx ->
st_regions A2 = st_regions A1 -> st_brk A2 = st_brk A1 -> ledger_ok B Lx A2 mdx.
Proof.
intros Lx A1' A2' mdx G ER EB.
assert (RO : forall k, region_of A2' k = region_of A1' k) by (intros k; unfold region_of; rewrite ER; reflexivity).
assert (NS : nslots A2' = nslots A1') by (unfold nslots; rewrite ER; reflexivity).
assert (LBy : live_bytes A2' = live_bytes A1') by (unfold live_bytes; rewrite ER; reflexivity).
split; try (exact (lg_reserved _ _ _ _ G) || exact (lg_limit _ _ _ _ G) || exact (lg_brk0 _ _ _ _ G)).
- intros k rg Hk. rewrite RO in Hk. exact (lg_maps _ _ _ _ G k rg Hk).
- intros k rg off Hk. rewrite RO in Hk. exact (lg_noaccess _ _ _ _ G k rg off Hk).
- rewrite EB. exact (lg_brk _ _ _ _ G).
- intros k rg Hk. rewrite RO in Hk. exact (lg_placed _ _ _ _ G k rg Hk).
- rewrite NS. exact (lg_count _ _ _ _ G).
- rewrite LBy. exact (lg_sizes _ _ _ _ G).
- rewrite LBy. exact (lg_backing _ _ _ _ G).
-   exact (lg_ceil _ _ _ _ G).
Qed.
Lemma layout_ok_same : forall Lx A1 A2, layout_ok Lx A1 -> st_regions A2 = st_regions A1 -> footprint A2 = footprint A1 -> layout_ok Lx A2.
Proof.
intros Lx A1' A2' (Y1 & Y2 & Y3' & Y4) ER EF. split; [exact Y1|]. split; [|rewrite EF; auto].
intros k rg Hk. unfold region_of in Hk. rewrite ER in Hk. exact (Y2 k rg Hk).
Qed.
Section D3.
Variable m : sptr.
Hypothesis X3m : X3 = [m].
Hypothesis Km : In m (keys A3).
Hypothesis Mm : MT A3 m = Some MRaw \/ MT A3 m = Some (MFree None None).
Hypothesis HB3 : bounded A3.
Hypothesis HA3 : ama_ok A3.
Variable sp : Z.
Hypothesis Hsp : alloc_ceiling + ALLOC_STACK <= sp.
Variable memF : word -> option byte.
Let g : Z := loc_addr L3 (LMem m).
Let am6 : ameta := am6 A n A3.
Let A6 : astate := A6 A n A3 m.
Let newc : list mcell := new_cells A n A3 m ++ group_tail_cells am6.
Hypothesis F0 : forall x, 0 <= x < 2 ^ 64 ->
~ ((sp - ALLOC_STACK <= x < sp) \/ (errno_addr B <= x < errno_addr B + 4)) ->
~ (ms_ctx B + CTX_mmap_counter <= x < ms_ctx B + CTX_mmap_counter + 4) ->
~ (g + 16 <= x < g + 40) ->
~ (bv_unsigned a <= x < bv_unsigned a + len) -> memF (Z_to_bv 64 x) = mem6 (Z_to_bv 64 x).
Hypothesis F1a : forall x, bv_unsigned a <= x < bv_unsigned a + len -> present memF x.
Hypothesis F1p : forall x, 0 <= x < alloc_ceiling -> ~ in_img B x -> present mem6 x -> present memF x.
Hypothesis NEWOK : forall c, In c newc -> cell_mem B L3 memF c.
Hypothesis WF6 : WF A6.
Variables ub1 ub2 : list (sptr * Z).
Hypothesis UB6 : user_blocks A6 = ub1 ++ (p6 A n A3, n) :: ub2 /\ user_blocks A = ub1 ++ ub2.
Let HI3m : Inv [m] None U0 A3.
Proof. rewrite <- X3m. exact HI3. Qed.
Let EU3m : forall g' am, usedX [m] A3 g' am <-> usedX [] A g' am.
Proof. intros g' am. rewrite <- (EU3 g' am), X3m. tauto. Qed.
Lemma m_home : exists r rg, region_of A3 r = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\ r <> r0 /\
ly_reg L3 r + reg_lo rg <= g /\ g + 40 <= ly_reg L3 r + rg_len rg /\ g mod 8 = 0 /\
4096 <= g /\ g + 40 <= alloc_ceiling /\ (forall x, g <= x < g + 40 -> ~ in_img B x).
Proof.
clear F0 F1a F1p NEWOK WF6 UB6. pose proof (inv_keys HI3) as (ND & KP & _ & _ & Hcnt).
destruct (KP m Km) as (ar & k & Har & Hk & Em).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb ar _); lia).
destruct (inv_areas HI3) as (_ & Hareas & _). destruct (Hareas ar Har) as (r & o & rg & -> & Hom & Ho & Hr & Hl & Hsz & Hkind).
exists r, rg. pose proof (lg_placed _ _ _ _ G3 r rg Hr Hl) as (Hal & Hlo & Hhi & Himg). pose proof (reg_lo_le rg).
assert (Eg : g = ly_reg L3 r + o + (AREA_HDR + META_SIZE * k)).
{ unfold g. rewrite Em. cbn [padd loc_addr]. lia. }
assert (Hkind' : rg_kind rg <> RkMap) by (intros E; rewrite E in Hkind; exact Hkind).
assert (Hr0 : r <> r0) by (intros ->; rewrite A3_r0 in Hr; injection Hr as <-; exact Hkind).
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
split; [exact Hr|]. split; [exact Hl|]. split; [exact Hkind'|]. split; [exact Hr0|].
split; [lia|]. split; [lia|]. split.
{ rewrite Eg. apply Z.mod_divide in Hal; [|lia]. apply Z.mod_divide in Hom; [|lia]. destruct Hal as [q1 Hq1]. destruct Hom as [q2 Hq2].
rewrite Hq1, Hq2. replace (q1 * 4096 + q2 * 4096 + (24 + 40 * k)) with ((q1 * 512 + q2 * 512 + 3 + 5 * k) * 8) by lia. apply Z_mod_mult. }
split; [lia|]. split; [lia|]. intros x Hx. apply Himg. lia.
Qed.
Lemma meta_old_cells_in : In (MCell (LMem (padd m META_prev)) 8 (VZ 0)) (image A3) /\ In (MCell (LMem (padd m META_next)) 8 (VZ 0)) (image A3).
Proof.
clear F0 F1a F1p NEWOK WF6 UB6. pose proof (inv_keys HI3) as (ND & KP & _ & _ & Hcnt).
destruct (KP m Km) as (ar & k & Har & Hk & Em).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb ar _); lia).
assert (CELLS : forall c, In c [MCell (LMem (padd m META_prev)) 8 (VZ 0); MCell (LMem (padd m META_next)) 8 (VZ 0)] -> In c (image A3)).
{ intros c Hc. unfold image. apply in_app_iff. right. apply in_app_iff. left.
apply (In_areas_cells_intro A3 (st_areas A3) ar c Har). intros next. unfold area_cells. apply in_app_iff. right.
apply in_flat_map. exists (Z.to_nat k). split; [apply in_seq; lia|].
rewrite Z2Nat.id by lia. rewrite <- Em. change (mlookup (st_metas A3) m) with (MT A3 m).
destruct Mm as [E|E]; rewrite E; cbn [meta_slot_cells optr In]; cbn [In] in Hc; destruct Hc as [<-|[<-|[]]]; tauto. }
split; apply CELLS; cbn; tauto.
Qed.
Lemma meta_old_cells : cell_mem B L3 mem6 (MCell (LMem (padd m META_prev)) 8 (VZ 0)) /\ cell_mem B L3 mem6 (MCell (LMem (padd m META_next)) 8 (VZ 0)).
Proof.
clear F0 F1a F1p NEWOK WF6 UB6. destruct meta_old_cells_in as [H1 H2]. pose proof (mid_mem _ _ _ _ _ MID3) as MM.
split; eapply memrep_cell; eauto.
Qed.
Lemma meta_present : forall x, g <= x < g + 40 -> present mem6 x.
Proof.
clear F0 F1a F1p NEWOK WF6 UB6. intros x Hx. pose proof (inv_keys HI3) as (ND & KP & _ & _ & Hcnt).
destruct (KP m Km) as (ar & k & Har & Hk & Em).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb ar _); lia).
pose proof (mid_mem _ _ _ _ _ MID3) as (_ & _ & FT).
assert (Hin : In (LMem ar, PGSZ) (footprint A3)) by (right; apply in_app_iff; left; apply in_map_iff; exists ar; auto).
pose proof (proj1 (Forall_forall _ _) FT _ Hin) as F. unfold foot_ok in F. cbn [fst snd] in F. apply F.
unfold g in Hx. rewrite Em in Hx. destruct ar as [r o]. cbn [padd loc_addr] in Hx |- *.
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
Qed.
Lemma ctr_cell6 : forall k, (k < 4)%nat ->
mbyte (ms_segs B) mem6 (ms_ctx B + CTX_mmap_counter + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (st_mmap_counter A) 4 k)).
Proof.
clear F0 F1a F1p NEWOK WF6 UB6. intros k Hk. destruct FR3 as (_ & _ & _ & _ & EC). pose proof (dA2_fields A n) as (_&_&_&_&_&EC2&_).
assert (Hin : In (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter A3))) (image A3)).
{ unfold image. apply in_app_iff. left. unfold ctx_cells. apply in_app_iff. left. cbn. tauto. }
pose proof (memrep_cell B L3 A3 mem6 _ (mid_mem _ _ _ _ _ MID3) Hin) as C. unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr sval_num] in C.
rewrite L3_ctx in C. rewrite EC, EC2 in C. apply C. exact Hk.
Qed.
Lemma old_block_facts : forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k ->
loc_addr L3 (LMem p) = loc_addr L (LMem p) /\
cell_home_ok (loc_addr L3 (LMem p) + i) /\ ~ in_img B (loc_addr L3 (LMem p) + i) /\
~ (g <= loc_addr L3 (LMem p) + i < g + 40) /\ ~ in_nonmap_region L3 A3 (loc_addr L3 (LMem p) + i).
Proof.
clear F0 F1a F1p NEWOK WF6 UB6. intros p k i Hb Hi.
destruct (block_region A p k HW Hb) as (kk & o & rg & -> & Hr & Hkind & Hl & Ho & Hk0 & Hlen & _).
pose proof (region_of_lt A kk rg Hr) as Hlt. pose proof (old_region_A3 _ _ Hr Hkind) as Hr3.
cbn [loc_addr]. rewrite (L3_old kk Hlt).
assert (RB : forall x, ly_reg L3 kk + reg_lo rg <= x < ly_reg L3 kk + rg_len rg -> cell_home_ok x /\ ~ in_img B x /\ ~ (g <= x < g + 40) /\ ~ in_nonmap_region L3 A3 x).
{ intros x Hx. assert (Hne : kk <> r0) by (unfold r0, YN2c.r0; lia).
pose proof (region_byte_ok kk rg x Hne Hr3 Hl Hx) as OK. split; [exact OK|].
pose proof (lg_placed _ _ _ _ G3 kk rg Hr3 Hl) as (_ & _ & _ & Himg). pose proof (reg_lo_le rg).
split; [apply Himg; lia|]. split.
- destruct m_home as (r & rg' & Hr' & Hl' & Hk' & _ & G1 & G2 & _).
assert (Hne2 : kk <> r) by (intros ->; rewrite Hr3 in Hr'; injection Hr' as <-; exact (Hk' Hkind)).
pose proof (reg_lo_le rg').
pose proof (lx_regs _ _ _ Y3 kk r rg rg' Hne2 Hr3 Hr' Hl Hl' ltac:(lia) ltac:(lia)) as D.
unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
- intros [_ NM]. apply NM. exists kk, rg. split; [exact Hr3|]. split; [exact Hl|]. split; [exact Hkind|].
pose proof (reg_lo_le rg). lia. }
split; [reflexivity|]. rewrite <- (L3_old kk Hlt). apply RB. unfold reg_lo. rewrite Hkind. lia.
Qed.
Lemma grant_bytes_ok : forall x, bv_unsigned a <= x < bv_unsigned a + len ->
~ (g <= x < g + 40) /\ ~ in_nonmap_region L3 A3 x /\ ~ in_img B x /\ 4096 <= x < alloc_ceiling.
Proof.
clear F0 F1a F1p NEWOK WF6 UB6. intros x Hx. pose proof r0_placed as (_ & Rlo & Rhi & Rimg). split; [|split; [|split; [apply Rimg; exact Hx | lia]]].
- destruct m_home as (r & rg' & Hr' & Hl' & Hk' & Hne & G1 & G2 & _). intros Hg.
exact (disjoint_r0 r rg' x Hne Hr' Hl' ltac:(lia) Hx).
- intros [_ NM]. apply NM. exists r0, (rgn len). split; [exact A3_r0|]. split; [reflexivity|]. split; [reflexivity|].
rewrite L3_r0. cbn [rg_len rgn YN2c.rgn]. exact Hx.
Qed.
Lemma new_cells_in_image : forall c, In c (new_cells A n A3 m) -> In c (image A6).
Proof.
intros c Hc. unfold new_cells in Hc. cbn [In] in Hc. rewrite in_app_iff in Hc.
destruct Hc as [<- | [Hc | Hc]].
- unfold image. apply in_app_iff. left. unfold ctx_cells. apply in_app_iff. left. cbn.
right. right. left. unfold A6, YN2f.A6, YN2f.A5, upd_meta. cbn. reflexivity.
- apply (meta_cells_in_image A6 m am6 c WF6); [|exact Hc]. unfold usedX, MTX. cbn [memb]. unfold A6. rewrite (MT_A6 A n A3 m m), sptr_eqb_refl. reflexivity.
- unfold image. rewrite !in_app_iff. right. right. apply in_flat_map. exists (m, am6). split; [|exact Hc].
apply (used_metas_iff A6 m am6 (proj1 (inv_keys WF6))). unfold A6. rewrite (MT_A6 A n A3 m m), sptr_eqb_refl. reflexivity.
Qed.
Definition chg_cells : list mcell :=
[MCell (LCtx CTX_mmap_counter) 4 (VZ (ctr5 A3));
MCell (LMem (padd m META_mem)) 8 (VP (am_mem am6));
MCell (LMem (padd m META_avail)) 4 (VZ (am_avail am6));
MCell (LMem (padd m META_freed)) 4 (VZ (am_freed am6));
MCell (LMem (padd m META_bits)) 8 (VZ (meta_bits am6))].
Lemma chg_cells_new : forall c, In c chg_cells -> In c (new_cells A n A3 m).
Proof.
intros c Hc. unfold chg_cells, new_cells in *. cbn [In meta_slot_cells app] in Hc |- *.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; tauto.
Qed.
Lemma chg_cover : forall x,
(ms_ctx B + CTX_mmap_counter <= x < ms_ctx B + CTX_mmap_counter + 4) \/ (g + 16 <= x < g + 40) ->
exists c, In c chg_cells /\ fst (cell_range L3 c) <= x < fst (cell_range L3 c) + snd (cell_range L3 c).
Proof.
intros x Hx. unfold chg_cells, cell_range. unfold META_mem, META_avail, META_freed, META_bits.
assert (Epadd : forall d, loc_addr L3 (LMem (padd m d)) = g + d) by (intros d; unfold g; destruct m; cbn; lia).
destruct Hx as [Hx|Hx].
- eexists. split; [left; reflexivity|]. cbn [fst snd mc_loc mc_w loc_addr]. rewrite L3_ctx. lia.
- destruct (Z_lt_le_dec x (g + 24)); [|destruct (Z_lt_le_dec x (g + 28)); [|destruct (Z_lt_le_dec x (g + 32))]].
+ eexists. split; [right; left; reflexivity|]. cbn [fst snd mc_loc mc_w]. rewrite Epadd. lia.
+ eexists. split; [right; right; left; reflexivity|]. cbn [fst snd mc_loc mc_w]. rewrite Epadd. lia.
+ eexists. split; [right; right; right; left; reflexivity|]. cbn [fst snd mc_loc mc_w]. rewrite Epadd. lia.
+ eexists. split; [right; right; right; right; left; reflexivity|]. cbn [fst snd mc_loc mc_w]. rewrite Epadd. lia.
Qed.
Lemma kept6 : forall x, cell_home_ok x ->
~ ((ms_ctx B + CTX_mmap_counter <= x < ms_ctx B + CTX_mmap_counter + 4) \/ (g + 16 <= x < g + 40)) ->
memF (Z_to_bv 64 x) = mem6 (Z_to_bv 64 x).
Proof.
intros x (H1 & H2 & H3 & H4) Hn'. pose proof (proj1 alloc_ceiling_val). apply F0; [lia | | tauto | tauto | exact H4].
intros [Hs|He]; [unfold ALLOC_STACK in *; lia | exact (H3 He)].
Qed.
Lemma footprint6 : footprint A6 = footprint A3.
Proof. exact (footprint_A6 A n A3 m Km). Qed.
Lemma layout_ok6 : layout_ok L3 A6.
Proof.
apply (layout_ok_same L3 A3 A6 (mid_layout _ _ _ _ _ MID3)); [| exact footprint6].
exact (proj1 (proj2 (proj2 (A6_fields A n A3 m Km)))).
Qed.
Lemma old_image_cell : forall c, In c (image A6) -> In c (image A3) ->
In c newc \/ forall j, (j < mc_w c)%nat ->
~ ((ms_ctx B + CTX_mmap_counter <= loc_addr L3 (mc_loc c) + Z.of_nat j < ms_ctx B + CTX_mmap_counter + 4) \/
(g + 16 <= loc_addr L3 (mc_loc c) + Z.of_nat j < g + 40)).
Proof.
intros c Hc Hold. pose proof (image_cells_disjoint A6 L3 WF6 layout_ok6) as PD.
assert (K : forall c', In c' chg_cells -> c = c' \/ ranges_disjoint (cell_range L3 c) (cell_range L3 c')).
{ intros c' Hc'. destruct (pairwise_map_In' ranges_disjoint (cell_range L3) (image A6) c c' PD Hc (new_cells_in_image c' (chg_cells_new c' Hc'))) as [E|[D|D]];
[left; exact E | right; exact D | right; apply ranges_disjoint_sym; exact D]. }
assert (NEWC : forall c', In c' chg_cells -> c = c' -> In c newc).
{ intros c' Hc' ->. unfold newc. apply in_app_iff. left. apply chg_cells_new. exact Hc'. }
destruct (K _ (or_introl eq_refl)) as [E|D1]; [left; eapply NEWC; [left; reflexivity | exact E]|].
destruct (K _ (or_intror (or_introl eq_refl))) as [E|D2]; [left; eapply NEWC; [right; left; reflexivity | exact E]|].
destruct (K _ (or_intror (or_intror (or_introl eq_refl)))) as [E|D3]; [left; eapply NEWC; [right; right; left; reflexivity | exact E]|].
destruct (K _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as [E|D4]; [left; eapply NEWC; [right; right; right; left; reflexivity | exact E]|].
destruct (K _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as [E|D5]; [left; eapply NEWC; [right; right; right; right; left; reflexivity | exact E]|].
right. intros j Hj Hx. destruct (chg_cover _ Hx) as (c' & Hin & Hr).
unfold ranges_disjoint in D1, D2, D3, D4, D5. unfold cell_range in *. cbn [fst snd] in *.
cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [mc_loc mc_w fst snd] in *; lia.
Qed.
Lemma memrep_A6 : memrep B L3 A6 memF.
Proof.
pose proof (mid_mem _ _ _ _ _ MID3) as (C1 & C2 & C3).
split; [|split].
- apply Forall_forall. intros c Hc.
destruct (image_A6 A n A3 m HI3m Km Mm c Hc) as [Hnew | Hold]; [apply NEWOK; unfold newc; apply in_app_iff; left; exact Hnew|].
destruct (old_image_cell c Hc Hold) as [Hnew | Hav]; [apply NEWOK; exact Hnew|].
eapply cell_mem_ext; [| exact (proj1 (Forall_forall _ _) C1 c Hold)].
intros j Hj. apply kept6; [apply cells_A3_home; [left; exact Hold | exact Hj] | exact (Hav j Hj)].
- apply Forall_forall. intros c Hc.
destruct (tail_cells_A6 A n A3 m HI3m Km c Hc) as [Hnew | Hold]; [apply NEWOK; unfold newc; apply in_app_iff; right; exact Hnew|].
eapply cell_mem_ext; [| exact (proj1 (Forall_forall _ _) C2 c Hold)].
intros j Hj. apply kept6; [apply cells_A3_home; [right; exact Hold | exact Hj] |].
rewrite tail_cells_A3 in Hold. destruct (tail_cell_region A HW c Hold) as (p & rg & E & Hr & Hkind & Hl & Ho & Hw).
rewrite E, loc_addr_LMem'. pose proof (old_region_A3 _ _ Hr Hkind) as Hr3.
pose proof (lg_placed _ _ _ _ G3 (prid p) rg Hr3 Hl) as (_ & _ & _ & Himg).
intros [Hx|Hx].
+ apply (Himg (ly_reg L3 (prid p) + poff p + Z.of_nat j)); [lia|]. apply (so_ctx_img _ (mid_syms _ _ _ _ _ MID3)). unfold CTX_mmap_counter, CTX_SIZE in *. lia.
+ destruct m_home as (r & rg' & Hr' & Hl' & Hk' & _ & G1 & G2 & _).
assert (Hne : prid p <> r) by (intros E2; rewrite E2 in Hr3; rewrite Hr3 in Hr'; injection Hr' as <-; exact (Hk' Hkind)).
pose proof (reg_lo_le rg').
pose proof (lx_regs _ _ _ Y3 (prid p) r rg rg' Hne Hr3 Hr' Hl Hl' ltac:(unfold reg_lo; rewrite Hkind; lia) ltac:(lia)) as D.
unfold ranges_disjoint, reg_lo in D. rewrite Hkind in D. cbn [fst snd] in D. unfold reg_lo in G1. lia.
- rewrite footprint6. destruct (footprint_split A3 eq_refl eq_refl (fun k _ => eq_refl) (or_intror eq_refl)) as (l1 & l2 & F3 & _).
rewrite F3. apply Forall_forall. intros e He.
apply in_app_iff in He as [He|[<-|He]].
2:{ unfold foot_ok, r0_entry. cbn [fst snd loc_addr]. rewrite L3_r0, Z.add_0_r. exact F1a. }
all: assert (He' : In e (l1 ++ l2)) by (apply in_app_iff; auto).
all: assert (He3 : In e (footprint A3)) by (rewrite F3; apply in_app_iff; apply in_app_iff in He' as [?|?]; [left | right; right]; assumption).
all: pose proof (proj1 (Forall_forall _ _) C3 e He3) as F; unfold foot_ok in F |- *; destruct (fst e) as [o|p] eqn:Efst; [exact I|];
intros x Hx; destruct (footprint_A3_disjoint l1 l2 e x F3 He' ltac:(rewrite Efst; exact Hx)) as [Hout Hne];
destruct (footprint_A3_home e x He3 Hne ltac:(rewrite Efst; exact Hx)) as [[E _] | (p' & _ & OK & NI)]; [congruence|];
apply F1p; [destruct OK as (OK1 & _); lia | exact NI | apply F; exact Hx].
Qed.
Let q : Z := bv_unsigned a + UNIT + UNIT * e_off n A3.
Lemma p6_addr : loc_addr L3 (LMem (p6 A n A3)) = q.
Proof. unfold p6. cbn [loc_addr]. fold r0. rewrite L3_r0. unfold q. lia. Qed.
Lemma stride_am6 : stride_of am6 = e_stride n.
Proof.
unfold am6, YN2f.am6. cbv zeta.
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (upd_slot_fields _ _ _)))))). apply (stride_am4 A n (proj1 Hn) (proj2 Hn)).
Qed.
Lemma new_tail_range : forall c j, In c (group_tail_cells am6) -> (j < mc_w c)%nat ->
q + n <= loc_addr L3 (mc_loc c) + Z.of_nat j < bv_unsigned a + len.
Proof.
intros c j Hc Hj.
pose proof (e_facts n A3 (proj1 Hn) m HI3m (proj2 Hn)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
pose proof stride_am6 as ST.
unfold group_tail_cells in Hc. cbn [In] in Hc.
assert (Emem : am_mem am6 = SP r0 0) by reflexivity.
assert (Elast : am_last am6 = 0) by reflexivity.
destruct Hc as [<- | Hc].
- cbn [mc_loc mc_w] in Hj |- *. rewrite Emem. unfold group_extent. rewrite ST, Elast. cbn [padd loc_addr]. fold r0. rewrite L3_r0.
unfold q, UNIT, IB in *. lia.
- rewrite Elast in Hc. change (flat_map (frame_tail_cells am6) (zseq 0 (0 + 1))) with (frame_tail_cells am6 0 ++ []) in Hc. rewrite app_nil_r in Hc.
unfold frame_tail_cells in Hc. change (nth_slot am6 0) with (mkSlot (Some (e_hdr n A3)) (Some (e_fr n A3))) in Hc. cbn [ss_fr fr_kind e_fr] in Hc.
assert (ER : reserved_of am6 (e_fr n A3) = e_reserved n A3).
{ unfold reserved_of, e_reserved. rewrite ST. cbn [fr_off fr_n e_fr]. reflexivity. }
rewrite ER in Hc.
assert (Efp : loc_addr L3 (LMem (padd (frame_ptr am6 0 (e_fr n A3)) (fr_n (e_fr n A3)))) = q + n).
{ unfold frame_ptr, slot_start. rewrite Emem, ST. cbn [fr_off fr_n e_fr padd loc_addr]. fold r0. rewrite L3_r0. unfold q. lia. }
assert (Ese : forall d, loc_addr L3 (LMem (padd (slot_end am6 0) d)) = bv_unsigned a + len - IB + d).
{ intros d. unfold slot_end, slot_start. rewrite Emem, ST. cbn [padd loc_addr]. fold r0. rewrite L3_r0. rewrite F8. unfold UNIT. lia. }
apply in_app_iff in Hc as [Hc|Hc].
+ destruct (0 <? e_reserved n A3) eqn:E; [|destruct Hc]. destruct Hc as [<-|[]]. cbn [mc_loc mc_w] in Hj |- *. rewrite Efp.
apply Z.ltb_lt in E. unfold e_reserved, q, UNIT, IB in *. lia.
+ destruct (5 <=? e_reserved n A3) eqn:E; [|destruct Hc]. apply Z.leb_le in E.
destruct Hc as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hj |- *; rewrite Ese; unfold e_reserved, q, UNIT, IB in *; lia.
Qed.
Lemma tail_geom_A6 : tail_geom L3 A6.
Proof.
pose proof (e_facts n A3 (proj1 Hn) m HI3m (proj2 Hn)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
assert (Hn0 : 0 <= n) by (pose proof (proj1 Hn) as T; unfold MMAP_THRESHOLD in T; lia).
destruct UB6 as [U6 UA].
assert (OLDB : forall b x, In b (ub1 ++ ub2) -> loc_addr L3 (LMem (fst b)) <= x < loc_addr L3 (LMem (fst b)) + snd b ->
~ (bv_unsigned a <= x < bv_unsigned a + len)).
{ intros [bp bn] x Hb Hx. rewrite <- UA in Hb. cbn [fst snd] in Hx.
destruct (block_region A bp bn HW Hb) as (k & o & rg & -> & Hr & Hkind & Hl & Ho & Hbn0 & Hlen' & _).
cbn [loc_addr] in Hx. pose proof (region_of_lt A k rg Hr) as Hlt.
apply (disjoint_r0 k rg x ltac:(unfold r0, YN2c.r0; lia) (old_region_A3 _ _ Hr Hkind) Hl). unfold reg_lo. rewrite Hkind. lia. }
unfold tail_geom. apply Forall_forall. intros c Hc j Hj.
destruct (tail_cells_A6 A n A3 m HI3m Km c Hc) as [Hnew | Hold].
- pose proof (new_tail_range c j Hnew Hj) as R. split.
+ exists r0_entry. rewrite footprint6. split; [exact r0_entry_in|]. unfold r0_entry. cbn [fst snd loc_addr]. fold r0. rewrite L3_r0. unfold q, UNIT in R. lia.
+ intros (b & Hb & Hbx). rewrite U6 in Hb. apply in_app_iff in Hb as [Hb|[<-|Hb]].
* apply (OLDB b _ ltac:(apply in_app_iff; left; exact Hb) Hbx). unfold q, UNIT in R. lia.
* cbn [fst snd] in Hbx. rewrite p6_addr in Hbx. lia.
* apply (OLDB b _ ltac:(apply in_app_iff; right; exact Hb) Hbx). unfold q, UNIT in R. lia.
- pose proof (proj1 (Forall_forall _ _) (mid_tailg _ _ _ _ _ MID3) c Hold j Hj) as [(e & He & Hx) Hnb].
pose proof (cells_A3_home c j (or_intror Hold) Hj) as (_ & _ & _ & Hout).
split.
+ exists e. rewrite footprint6. auto.
+ intros (b & Hb & Hbx). rewrite U6 in Hb. apply in_app_iff in Hb as [Hb|[<-|Hb]].
* apply Hnb. exists b. rewrite user_blocks_A3, UA. split; [apply in_app_iff; left; exact Hb | exact Hbx].
* cbn [fst snd] in Hbx. rewrite p6_addr in Hbx. unfold q, UNIT, IB in *. lia.
* apply Hnb. exists b. rewrite user_blocks_A3, UA. split; [apply in_app_iff; right; exact Hb | exact Hbx].
Qed.
Lemma statics_A6 : statics_ok B memF.
Proof.
apply (statics_ok_ext mem6); [| exact (mid_statics _ _ _ _ _ MID3)].
intros x Hs. destruct (static_byte_ok x Hs) as (H1 & H2 & H3). pose proof (proj1 alloc_ceiling_val).
pose proof (so_statics_img _ (mid_syms _ _ _ _ _ MID3) x Hs) as Hi.
destruct m_home as (r & rg' & _ & _ & _ & _ & _ & _ & _ & _ & _ & NI).
apply F0; [lia | | | | exact H3].
- intros [Hs'|He]; [unfold ALLOC_STACK in *; lia | exact (H2 He)].
- intros Hx. apply (SNC x Hs). unfold CTX_mmap_counter, CTX_SIZE in *. lia.
- intros Hx. apply (NI x); [lia | exact Hi].
Qed.
Lemma span_ok_A6 : span_ok A6.
Proof.
unfold A6, YN2f.A6, YN2f.A5, YN2f.A4s.
apply span_ok_upd_used; [| apply am_span_ok_sc; cbn; lia].
apply span_ok_set_mmap_counter. apply span_ok_upd_used; [exact span_ok_A3 | apply am_span_ok_sc; cbn; lia].
Qed.
Theorem MRx_A6 : MRx B L3 A6 memF md3.
Proof.
pose proof (A6_fields A n A3 m Km) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & _).
pose proof (e_facts n A3 (proj1 Hn) m HI3m (proj2 Hn)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
apply midrep_MRx.
- destruct (mid_md _ _ _ _ _ MID3) as (H1 & H2 & H3). split.
+ exact (mid_syms _ _ _ _ _ MID3).
+ exact memrep_A6.
+ exact tail_geom_A6.
+ exact statics_A6.
+ exact (ledger_ok_same L3 A3 A6 md3 G3 E3 E9).
+ exact (ledger_x_same_regions L3 A3 A6 md3 md3 Y3 E3 eq_refl eq_refl).
+ exact layout_ok6.
+ exact (mid_ctx _ _ _ _ _ MID3).
+ exact (mid_sec _ _ _ _ _ MID3).
+ auto.
- exact WF6.
- exact (bounded_A6 A n A3 m Km Mm HB3).
- intros g' am i fr Hf Hk. destruct (frames_A6 A n A3 m HI3m Km _ Hf) as [E | Hold].
+ injection E as -> -> -> ->.
pose proof stride_am6 as ST.
unfold reserved_of. fold am6. rewrite ST. cbn [fr_off fr_n e_fr]. fold (e_reserved n A3). unfold PGSZ in F6.
change (e_stride n - IB - UNIT * e_off n A3 - n) with (e_reserved n A3). lia.
+ rewrite frames_A3 in Hold. exact (MRx_rsv _ _ _ _ _ MX g' am i fr Hold Hk).
- exact (ama_A6 A n A3 m Km Mm HA3).
-
exact span_ok_A6.
Qed.
End D3.
End DM.
Lemma D2_pack : forall B L A mem md (a : word) n L3 A3 mem6 md3 sp mem8,
MRx B L A mem md -> MMAP_THRESHOLD <= n < 2 ^ 62 -> grant_ok (Z_to_bv 64 0) md a (dlen n) = true ->
(forall x, errno_addr B <= x < errno_addr B + 4 -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE)) ->
(forall x, errno_addr B <= x < errno_addr B + 4 -> ~ static_owned B x) ->
(forall x, errno_addr B <= x < errno_addr B + 4 -> in_img B x) ->
(forall x, static_owned B x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE)) ->
midrep B L3 A3 mem6 md3 -> layout_le (dA2 A n) (L1 L A a) L3 -> am_frame (dA2 A n) A3 -> ub_same (dA2 A n) A3 ->
Inv [] None U0 A3 -> (forall g am, usedX [] A3 g am <-> usedX [] A g am) ->
alloc_ceiling + ALLOC_STACK <= sp ->
(forall x, 0 <= x < 2 ^ 64 -> ~ ((sp - ALLOC_STACK <= x < sp) \/ (errno_addr B <= x < errno_addr B + 4)) ->
~ (bv_unsigned a <= x < bv_unsigned a + dlen n) -> mem8 (Z_to_bv 64 x) = mem6 (Z_to_bv 64 x)) ->
bounded A3 -> ama_ok A3 ->
(exists vm3, md3 = with_vmmaps vm3 (md1 md a (dlen n))) ->
MRx B L3 (dm_kill A A3) mem8 (munmap_model a (Z_to_bv 64 (dlen n)) md3) /\
user_blocks (dm_kill A A3) = user_blocks A /\
(exists vm', munmap_model a (Z_to_bv 64 (dlen n)) md3 = with_vmmaps vm' md) /\
ly_reg L3 (r0 A) = bv_unsigned a /\ (forall k, (k < r0 A)%nat -> ly_reg L3 k = ly_reg L k) /\
region_of A3 (r0 A) = Some (rgn (dlen n)) /\
In (a, Z_to_bv 64 (dlen n)) (vm_maps (m_vmmaps md3)) /\
user_blocks A3 = user_blocks A.
Proof.
intros B L A mem md a n L3 A3 mem6 md3 sp mem8 MX Hn GR ENC ENS ERRIMG SNC MID3 LE3 FR3 UB3 HI3 EU3 Hsp AG8 HB3 HA3 VM3.
assert (HX3 : forall g am, memb g [] = true -> MT A3 g <> Some (MUsed am)) by (intros g am H; discriminate).
Ltac fin := first [eassumption | reflexivity].
split; [eapply MRx_A4; fin|].
split; [eapply user_blocks_A4; fin|].
split; [eapply md4_with; fin|].
split; [eapply L3_r0; fin|].
split; [eapply L3_old; fin|].
split; [eapply A3_r0; fin|].
split; [eapply r0_maps_entry; fin|].
eapply user_blocks_A3; fin.
Qed.
Lemma D3_pre : forall B L A mem md (a : word) n L3 A3 mem6 md3 m,
MRx B L A mem md -> MMAP_THRESHOLD <= n < 2 ^ 62 -> grant_ok (Z_to_bv 64 0) md a (dlen n) = true ->
(forall x, errno_addr B <= x < errno_addr B + 4 -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE)) ->
(forall x, errno_addr B <= x < errno_addr B + 4 -> ~ static_owned B x) ->
(forall x, errno_addr B <= x < errno_addr B + 4 -> in_img B x) ->
(forall x, static_owned B x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE)) ->
midrep B L3 A3 mem6 md3 -> layout_le (dA2 A n) (L1 L A a) L3 -> am_frame (dA2 A n) A3 -> ub_same (dA2 A n) A3 ->
Inv [m] None U0 A3 -> (forall g am, usedX [m] A3 g am <-> usedX [] A g am) ->
In m (keys A3) -> (MT A3 m = Some MRaw \/ MT A3 m = Some (MFree None None)) ->
let g := loc_addr L3 (LMem m) in
(exists r rg, region_of A3 r = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\ r <> r0 A /\
ly_reg L3 r + reg_lo rg <= g /\ g + 40 <= ly_reg L3 r + rg_len rg /\ g mod 8 = 0 /\
4096 <= g /\ g + 40 <= alloc_ceiling /\ (forall x, g <= x < g + 40 -> ~ in_img B x)) /\
(cell_mem B L3 mem6 (MCell (LMem (padd m META_prev)) 8 (VZ 0)) /\ cell_mem B L3 mem6 (MCell (LMem (padd m META_next)) 8 (VZ 0))) /\
(forall x, g <= x < g + 40 -> present mem6 x) /\
(forall k, (k < 4)%nat -> mbyte (ms_segs B) mem6 (ms_ctx B + CTX_mmap_counter + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (st_mmap_counter A) 4 k))) /\
(forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k ->
loc_addr L3 (LMem p) = loc_addr L (LMem p) /\
cell_home_ok B a n (loc_addr L3 (LMem p) + i) /\ ~ in_img B (loc_addr L3 (LMem p) + i) /\
~ (g <= loc_addr L3 (LMem p) + i < g + 40) /\ ~ in_nonmap_region L3 A3 (loc_addr L3 (LMem p) + i)) /\
(forall x, bv_unsigned a <= x < bv_unsigned a + dlen n ->
~ (g <= x < g + 40) /\ ~ in_nonmap_region L3 A3 x /\ ~ in_img B x /\ 4096 <= x < alloc_ceiling) /\
ly_reg L3 (r0 A) = bv_unsigned a /\ (forall k, (k < r0 A)%nat -> ly_reg L3 k = ly_reg L k) /\
user_blocks A3 = user_blocks A /\ loc_addr L3 (LMem (p6 A n A3)) = bv_unsigned a + UNIT + UNIT * e_off n A3.
Proof.
intros B L A mem md a n L3 A3 mem6 md3 m MX Hn GR ENC ENS ERRIMG SNC MID3 LE3 FR3 UB3 HI3 EU3 Km Mm g.
assert (HX3 : forall g' am, memb g' [m] = true -> MT A3 g' <> Some (MUsed am)).
{ intros g' am Hg'. cbn in Hg'. destruct (sptr_eqb g' m) eqn:E; [|discriminate]. apply sptr_eqb_eq in E. subst g'.
intros H. destruct Mm as [E2|E2]; rewrite E2 in H; discriminate. }
split; [eapply m_home; fin|].
split; [eapply meta_old_cells; fin|].
split; [eapply meta_present; fin|].
split; [eapply ctr_cell6; fin|].
split; [eapply old_block_facts; fin|].
split; [eapply grant_bytes_ok; fin|].
split; [eapply L3_r0; fin|].
split; [eapply L3_old; fin|].
split; [eapply user_blocks_A3; fin|].
eapply p6_addr; fin.
Qed.
Lemma D3_post : forall B L A mem md (a : word) n L3 A3 mem6 md3 m sp memF ub1 ub2,
MRx B L A mem md -> MMAP_THRESHOLD <= n < 2 ^ 62 -> grant_ok (Z_to_bv 64 0) md a (dlen n) = true ->
(forall x, errno_addr B <= x < errno_addr B + 4 -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE)) ->
(forall x, errno_addr B <= x < errno_addr B + 4 -> ~ static_owned B x) ->
(forall x, errno_addr B <= x < errno_addr B + 4 -> in_img B x) ->
(forall x, static_owned B x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE)) ->
midrep B L3 A3 mem6 md3 -> layout_le (dA2 A n) (L1 L A a) L3 -> am_frame (dA2 A n) A3 -> ub_same (dA2 A n) A3 ->
Inv [m] None U0 A3 -> (forall g am, usedX [m] A3 g am <-> usedX [] A g am) ->
In m (keys A3) -> (MT A3 m = Some MRaw \/ MT A3 m = Some (MFree None None)) ->
bounded A3 -> ama_ok A3 -> alloc_ceiling + ALLOC_STACK <= sp ->
let g := loc_addr L3 (LMem m) in
(forall x, 0 <= x < 2 ^ 64 ->
~ ((sp - ALLOC_STACK <= x < sp) \/ (errno_addr B <= x < errno_addr B + 4)) ->
~ (ms_ctx B + CTX_mmap_counter <= x < ms_ctx B + CTX_mmap_counter + 4) ->
~ (g + 16 <= x < g + 40) ->
~ (bv_unsigned a <= x < bv_unsigned a + dlen n) -> memF (Z_to_bv 64 x) = mem6 (Z_to_bv 64 x)) ->
(forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> present memF x) ->
(forall x, 0 <= x < alloc_ceiling -> ~ in_img B x -> present mem6 x -> present memF x) ->
(forall c, In c (new_cells A n A3 m ++ group_tail_cells (am6 A n A3)) -> cell_mem B L3 memF c) ->
WF (A6 A n A3 m) ->
user_blocks (A6 A n A3 m) = ub1 ++ (p6 A n A3, n) :: ub2 /\ user_blocks A = ub1 ++ ub2 ->
MRx B L3 (A6 A n A3 m) memF md3.
Proof.
intros B L A mem md a n L3 A3 mem6 md3 m sp memF ub1 ub2 MX Hn GR ENC ENS ERRIMG SNC MID3 LE3 FR3 UB3 HI3 EU3 Km Mm HB3 HA3 Hsp g F0 F1a F1p NEWOK WF6 UB6.
assert (HX3 : forall g' am, memb g' [m] = true -> MT A3 g' <> Some (MUsed am)).
{ intros g' am Hg'. cbn in Hg'. destruct (sptr_eqb g' m) eqn:E; [|discriminate]. apply sptr_eqb_eq in E. subst g'.
intros H. destruct Mm as [E2|E2]; rewrite E2 in H; discriminate. }
eapply MRx_A6; first [eassumption | reflexivity].
Qed.
End u.
