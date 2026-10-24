(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0h YK0i YK15 YM06 YM02 YP09 YK0v YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0x YO0z YO0s YO0v YO10 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN2b YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma live_bytes_app : forall l1 l2, State.live_bytes (l1 ++ l2) = State.live_bytes l1 + State.live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH. lia. Qed.
Lemma live_bytes_nonneg_maps : forall l, 0 <= State.live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (u64_range n). lia. Qed.
Lemma maps_subtract_app : forall l1 l2 lo hi, maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof. induction l1 as [|[a n] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.
Lemma maps_subtract_all_app : forall cuts l1 l2,
maps_subtract_all (l1 ++ l2) cuts = maps_subtract_all l1 cuts ++ maps_subtract_all l2 cuts.
Proof.
induction cuts as [|[a n] cuts IH]; intros; cbn; [reflexivity|]. rewrite maps_subtract_app. apply IH.
Qed.
Lemma iv_subtract_le : forall a sz lo hi, lo <= hi -> State.live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
intros a sz lo hi Hle. pose proof (u64_range a). pose proof (u64_range sz).
unfold iv_subtract. cbv zeta.
destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2; cbn [app State.live_bytes];
try apply Z.ltb_lt in E1; try apply Z.ltb_ge in E1; try apply Z.ltb_lt in E2; try apply Z.ltb_ge in E2;
rewrite ?u64_of_Z; try lia.
Qed.
Lemma maps_subtract_le : forall l lo hi, lo <= hi -> State.live_bytes (maps_subtract l lo hi) <= State.live_bytes l.
Proof.
induction l as [|[a n] l IH]; intros lo hi Hle; cbn; [lia|]. rewrite live_bytes_app.
pose proof (iv_subtract_le a n lo hi Hle). specialize (IH lo hi Hle). lia.
Qed.
Lemma maps_subtract_all_le : forall cuts l, State.live_bytes (maps_subtract_all l cuts) <= State.live_bytes l.
Proof.
induction cuts as [|[a n] cuts IH]; intros l; cbn; [lia|].
pose proof (u64_range n). specialize (IH (maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n))).
pose proof (maps_subtract_le l (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ltac:(lia)). lia.
Qed.
Lemma vm_backing_used_mmap : forall a n md,
vm_backing_used (mmap_model a n md) <= vm_backing_used md + bv_unsigned n.
Proof.
intros a n md. unfold vm_backing_used, mmap_model, with_vmmaps, vm_backed_maps, m_vmmaps, m_vm_lazy, m_vm_materialized. cbn.
change ((a, n) :: vm_maps (vmst_maps (m_vm md))) with ([(a, n)] ++ vm_maps (vmst_maps (m_vm md))).
rewrite !maps_subtract_all_app, !live_bytes_app.
pose proof (maps_subtract_all_le (vmst_lazy (m_vm md)) (maps_subtract_all [(a, n)] (vm_noaccess (vmst_maps (m_vm md))))).
pose proof (maps_subtract_all_le (vm_noaccess (vmst_maps (m_vm md))) [(a, n)]). cbn [State.live_bytes] in H0. lia.
Qed.
Lemma region_free_In : forall l (a n : word) e,
region_free l a n = true -> In e l -> 0 < bv_unsigned n -> 0 < bv_unsigned (snd e) ->
ranges_disjoint (bv_unsigned a, bv_unsigned n) (bv_unsigned (fst e), bv_unsigned (snd e)).
Proof.
induction l as [|[b s] l IH]; intros a n e H Hin Hn Hs; [destruct Hin|].
cbn [region_free] in H. apply andb_prop in H as [H1 H2].
destruct Hin as [<- | Hin]; [| apply IH; assumption].
cbn [fst snd] in *. apply negb_true_iff in H1. unfold iv_overlap in H1.
apply andb_false_iff in H1. unfold ranges_disjoint. cbn [fst snd].
destruct H1 as [H1 | H1]; apply Z.ltb_ge in H1; lia.
Qed.
Definition refs_below (n : nat) (c : mcell) : Prop :=
(match mc_loc c with LMem p => (prid p < n)%nat | LCtx _ => True end) /\
(match mc_val c with VP p => (prid p < n)%nat | _ => True end).
Definition ptrs_below (A : astate) : Prop :=
forall c, In c (image A) \/ In c (tail_cells A) -> refs_below (length (st_regions A)) c.
Section D1.
Variable B : malloc_syms.
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model).
Variables (a : word) (len : Z).
Hypothesis MX : MRx B L A mem md.
Hypothesis Hlen : 0 < len /\ len mod PGSZ = 0.
Hypothesis GR : grant_ok (Z_to_bv 64 0) md a len = true.
Definition r0 : nat := length (st_regions A).
Definition rgn : YO0i.region := YO0i.mkRegion RkMap len [] true.
Definition A1 : astate := set_regions (st_regions A ++ [rgn]) A.
Definition L1 : layout :=
Layout (ly_ctx L) (fun k => if Nat.eqb k r0 then bv_unsigned a else ly_reg L k) (ly_brk0 L) (ly_sec L).
Definition md1 : Model := mmap_model a (Z_to_bv 64 len) md.
Definition seqf (s : astate) : astate :=
if st_seq s =? 255 then set_seq 1 (set_unmap_seq (repeat 0 32) s) else set_seq (st_seq s + 1) s.
Definition A2 : astate := seqf A1.
Let M : MRc B L A mem md := MRx_MRc _ _ _ _ _ MX.
Lemma grant_facts :
bv_unsigned a mod PGSZ = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + len <= alloc_ceiling /\
region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a (Z_to_bv 64 len) = true /\
vm_backing_used md + len <= vm_limit (m_vmmaps md).
Proof.
destruct (grant_ok_unpack _ _ _ _ GR) as (Hal & Hpos & Htop & RF & Hbk).
unfold page_size in Hal. unfold PGSZ in *.
assert (Hceil : bv_unsigned a + len <= alloc_ceiling).
{ apply (YM05.grant_below_ceil (alloc_top (m_vmmaps md))).
- exact (lg_ceil _ _ _ _ (mc_ledger _ _ _ _ _ M)).
- rewrite Z.add_mod, Hal, (proj2 Hlen) by lia. reflexivity.
- exact Htop. }
repeat split; assumption.
Qed.
Lemma len_u : bv_unsigned (Z_to_bv 64 len) = len.
Proof. pose proof grant_facts as (_ & _ & H & _). pose proof (proj1 alloc_ceiling_val). pose proof (u64_range a). apply u64_of_Z. lia. Qed.
Lemma A2_regions : st_regions A2 = st_regions A ++ [rgn].
Proof. unfold A2, seqf, A1. destruct (st_seq _ =? 255); reflexivity. Qed.
Lemma A2_metas : st_metas A2 = st_metas A.
Proof. unfold A2, seqf, A1. destruct (st_seq _ =? 255); reflexivity. Qed.
Lemma A2_areas : st_areas A2 = st_areas A.
Proof. unfold A2, seqf, A1. destruct (st_seq _ =? 255); reflexivity. Qed.
Lemma region_of_A2 : forall k,
region_of A2 k = if (k <? r0)%nat then region_of A k else if Nat.eqb k r0 then Some rgn else None.
Proof.
intros k. unfold region_of. rewrite A2_regions. unfold r0.
destruct (Nat.ltb_spec k (length (st_regions A))).
- apply nth_error_app1. exact H.
- rewrite nth_error_app2 by lia. destruct (Nat.eqb_spec k (length (st_regions A))).
+ subst. rewrite Nat.sub_diag. reflexivity.
+ destruct (k - length (st_regions A))%nat as [|m] eqn:E; [lia|]. cbn. destruct m; reflexivity.
Qed.
Lemma region_of_A_lt : forall k rg, region_of A k = Some rg -> (k < r0)%nat.
Proof. intros k rg H. unfold r0. apply (region_of_lt A k rg H). Qed.
Lemma layout_le_L1 : layout_le A L L1.
Proof.
repeat split; try reflexivity. intros k Hk. cbn. unfold r0.
destruct (Nat.eqb_spec k (length (st_regions A))); [lia | reflexivity].
Qed.
Lemma L1_old : forall k rg, region_of A k = Some rg -> ly_reg L1 k = ly_reg L k.
Proof. intros k rg H. apply layout_le_L1. apply (region_of_lt A k rg H). Qed.
Lemma L1_new : ly_reg L1 r0 = bv_unsigned a.
Proof. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma loc_addr_L1 : forall l, (forall o, l <> LMem (SP r0 o)) -> loc_addr L1 l = loc_addr L l.
Proof.
intros [o|[k o]] H; cbn; [reflexivity|]. unfold r0 in *.
destruct (Nat.eqb_spec k (length (st_regions A))); [| reflexivity]. subst. exfalso. eapply H. reflexivity.
Qed.
Lemma flat_map_ext_in {X Y} (f g : X -> list Y) (l : list X) :
(forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
induction l as [|x l IH]; intros H; cbn; [reflexivity|].
rewrite H by (left; reflexivity). rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.
Lemma footprint_A2 : footprint A2 = footprint A ++ [(LMem (SP r0 0), len)].
Proof.
unfold footprint. rewrite A2_areas, A2_regions. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, flat_map_app.
cbn [flat_map]. rewrite app_nil_r.
rewrite region_of_A2. fold r0. rewrite Nat.ltb_irrefl, Nat.eqb_refl. cbn [rgn rg_kind rg_live rg_len].
rewrite (flat_map_ext_in _ (fun k => match region_of A k with
| Some rg => match rg_kind rg with RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else [] | _ => [] end
| None => [] end)).
2:{ intros k Hk. apply in_seq in Hk. rewrite region_of_A2. unfold r0 in *. rewrite (proj2 (Nat.ltb_lt _ _)) by lia. reflexivity. }
cbn [app]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma used_metas_A2 : used_metas A2 = used_metas A.
Proof. unfold used_metas. rewrite A2_metas. reflexivity. Qed.
Lemma tail_cells_A2 : tail_cells A2 = tail_cells A.
Proof. unfold tail_cells. rewrite used_metas_A2. reflexivity. Qed.
Lemma user_blocks_A2 : user_blocks A2 = user_blocks A.
Proof. unfold user_blocks. rewrite used_metas_A2. reflexivity. Qed.
Lemma frames_A2 : frames A2 = frames A.
Proof. unfold frames. rewrite used_metas_A2. reflexivity. Qed.
Lemma areas_cells_metas : forall s s' l, st_metas s' = st_metas s -> areas_cells s' l = areas_cells s l.
Proof.
intros s s' l E. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. f_equal.
unfold area_cells. rewrite E. reflexivity.
Qed.
Lemma image_A2 : image A2 = ctx_cells A2 ++ (areas_cells A (st_areas A) ++ flat_map (fun gm => group_cells (fst gm) (snd gm)) (used_metas A)).
Proof. unfold image. rewrite used_metas_A2, A2_areas, (areas_cells_metas A A2 _ A2_metas). reflexivity. Qed.
Lemma image_A : image A = ctx_cells A ++ (areas_cells A (st_areas A) ++ flat_map (fun gm => group_cells (fst gm) (snd gm)) (used_metas A)).
Proof. reflexivity. Qed.
Let X : ledger_x L A md := MRx_ledger_x _ _ _ _ _ MX.
Let G : ledger_ok B L A md := mc_ledger _ _ _ _ _ M.
Lemma new_disjoint_entry : forall e, In e (vm_maps (m_vmmaps md)) ->
ranges_disjoint (bv_unsigned a, len) (iv_lo e, iv_len e).
Proof.
intros e He. pose proof grant_facts as (_ & _ & _ & RF & _).
destruct (lx_maps _ _ _ X e He) as [P _].
pose proof (region_free_In _ a (Z_to_bv 64 len) e RF ltac:(apply in_app_iff; right; exact He) ltac:(rewrite len_u; lia) P) as D.
rewrite len_u in D. exact D.
Qed.
Lemma new_disjoint_img : forall x, in_img B x -> ~ (bv_unsigned a <= x < bv_unsigned a + len).
Proof.
intros x [_ (sg & Hsg & Hx)] Hin. pose proof grant_facts as (_ & _ & _ & RF & _).
rewrite <- (lg_reserved _ _ _ _ G) in Hsg.
pose proof (region_free_In _ a (Z_to_bv 64 len) sg RF ltac:(apply in_app_iff; left; exact Hsg) ltac:(rewrite len_u; lia) ltac:(lia)) as D.
rewrite len_u in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma new_disjoint_region : forall k rg x, region_of A k = Some rg -> rg_live rg = true ->
ly_reg L k + reg_lo rg <= x < ly_reg L k + rg_len rg -> ~ (bv_unsigned a <= x < bv_unsigned a + len).
Proof.
intros k rg x Hk Hl Hx Hin. destruct (lx_cov _ _ _ X k rg x Hk Hl Hx) as (e & He & Hex).
pose proof (new_disjoint_entry e He) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma new_disjoint_footprint : forall rg x, In rg (footprint A) ->
loc_addr L (fst rg) <= x < loc_addr L (fst rg) + snd rg -> ~ (bv_unsigned a <= x < bv_unsigned a + len).
Proof.
intros rg x Hin Hx.
destruct (In_footprint_inv A rg Hin) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
- apply new_disjoint_img. apply (so_ctx_img _ (mc_syms _ _ _ _ _ M)). rewrite (mc_ctx _ _ _ _ _ M) in Hx. lia.
- destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & Hareas & _).
destruct (Hareas ar Har) as (k & o & r & -> & _ & Ho & Hr & Hl & Hlen2 & _). cbn [loc_addr] in Hx.
apply (new_disjoint_region k r x Hr Hl). unfold reg_lo. destruct (rg_kind r); unfold PGSZ in *; lia.
- apply (new_disjoint_region k r x Hr Hl). unfold reg_lo. rewrite Hk. lia.
Qed.
Lemma live_bytes_A2 : live_bytes A2 = live_bytes A + len.
Proof.
unfold live_bytes. rewrite A2_regions.
induction (st_regions A) as [|x l IH]; cbn; [lia|]. rewrite IH. destruct (rg_live x); lia.
Qed.
Lemma nslots_A2 : nslots A2 = nslots A + 1.
Proof.
unfold nslots. rewrite A2_regions.
induction (st_regions A) as [|x l IH]; cbn -[region_slots]; [| rewrite IH; lia].
unfold region_slots, rgn. cbn. lia.
Qed.
Lemma live_bytes_nonneg : 0 <= live_bytes A.
Proof.
destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & _ & _ & _ & _ & _ & _ & _ & Hnn). unfold live_bytes. unfold region_of in Hnn.
assert (GG : forall l, (forall k rg, nth_error l k = Some rg -> 0 <= rg_len rg) ->
0 <= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l).
{ induction l as [|x l IH]; intros Hl; cbn; [lia|].
assert (0 <= rg_len x) by (apply (Hl 0%nat x); reflexivity).
assert (0 <= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l)
by (apply IH; intros k rg Hk; apply (Hl (S k) rg); exact Hk).
destruct (rg_live x); lia. }
apply GG. exact Hnn.
Qed.
Lemma region_len_le_live : forall s k rg,
(forall k rg, region_of s k = Some rg -> 0 <= rg_len rg) ->
region_of s k = Some rg -> rg_live rg = true -> rg_len rg <= live_bytes s.
Proof.
intros s k rg Hnn Hk Hl. unfold live_bytes. unfold region_of in *. revert k Hk.
assert (GG : forall l, (forall k rg, nth_error l k = Some rg -> 0 <= rg_len rg) ->
0 <= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l).
{ induction l as [|x l IH]; intros Hl'; cbn; [lia|].
assert (0 <= rg_len x) by (apply (Hl' 0%nat x); reflexivity).
assert (0 <= fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 l)
by (apply IH; intros k rg' Hk; apply (Hl' (S k) rg'); exact Hk).
destruct (rg_live x); lia. }
induction (st_regions s) as [|x l IH]; intros k Hk; [destruct k; discriminate|].
cbn. destruct k as [|k]; cbn in Hk.
- injection Hk as ->. rewrite Hl. pose proof (GG l ltac:(intros k rg' Hk'; apply (Hnn (S k) rg'); exact Hk')). lia.
- assert (0 <= rg_len x) by (apply (Hnn 0%nat x); reflexivity).
specialize (IH ltac:(intros k' rg' Hk'; apply (Hnn (S k') rg'); exact Hk') k Hk). destruct (rg_live x); lia.
Qed.
Lemma map_contains_cons : forall e l lo n, map_contains l lo n = true -> map_contains (e :: l) lo n = true.
Proof. intros e l lo n H. unfold map_contains in *. cbn. rewrite H. apply orb_true_r. Qed.
Lemma ledger_ok_A2 : ledger_ok B L1 A2 md1.
Proof.
pose proof grant_facts as (Hal & Hpos & Hceil & RF & Hbud). pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a).
assert (VM : vm_maps (m_vmmaps md1) = (a, Z_to_bv 64 len) :: vm_maps (m_vmmaps md)) by reflexivity.
assert (EB : st_brk A2 = st_brk A) by (unfold A2, seqf, A1; destruct (st_seq _ =? 255); reflexivity).
split; rewrite ?VM.
- exact (lg_reserved _ _ _ _ G).
- exact (lg_limit _ _ _ _ G).
- intros k rg Hk Hl Hkind. rewrite region_of_A2 in Hk.
destruct (Nat.ltb_spec k r0).
+ right. rewrite (L1_old k rg Hk). exact (lg_maps _ _ _ _ G k rg Hk Hl Hkind).
+ destruct (Nat.eqb_spec k r0); [|discriminate]. injection Hk as <-. subst k. left. unfold w64. rewrite L1_new, Z_to_bv_bv_unsigned. reflexivity.
- intros k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw. rewrite region_of_A2 in Hk.
destruct (Nat.ltb_spec k r0).
+ unfold w64 in *. rewrite (L1_old k rg Hk). destruct (lg_noaccess _ _ _ _ G k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw) as [N1 N2].
split; [exact N1 | apply map_contains_cons; exact N2].
+ destruct (Nat.eqb_spec k r0); [|discriminate]. injection Hk as <-. discriminate.
- exact (lg_brk0 _ _ _ _ G).
- rewrite EB. pose proof (lg_brk _ _ _ _ G) as HB.
destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & _ & _ & _ & _ & _ & Hbrk & _).
revert HB Hbrk. destruct (st_brk A) as [| |k p]; intros HB Hbrk; try exact HB.
destruct Hbrk as (_ & rg & Hrg & _). rewrite (L1_old k rg Hrg). exact HB.
- intros k rg Hk Hl. rewrite region_of_A2 in Hk.
destruct (Nat.ltb_spec k r0).
+ rewrite (L1_old k rg Hk). exact (lg_placed _ _ _ _ G k rg Hk Hl).
+ destruct (Nat.eqb_spec k r0); [|discriminate]. injection Hk as <-. subst k. rewrite L1_new. cbn [rgn rg_len].
split; [exact Hal|]. split; [unfold PGSZ in Hal; apply Z.mod_divide in Hal; [destruct Hal as [q Hq]; lia | lia]|].
split; [exact Hceil|]. intros x Hx Himg. exact (new_disjoint_img x Himg Hx).
- cbn [length]. rewrite nslots_A2. pose proof (lg_count _ _ _ _ G). lia.
- rewrite live_bytes_A2. constructor.
+ cbn [snd]. rewrite len_u. pose proof live_bytes_nonneg. lia.
+ apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (lg_sizes _ _ _ _ G) e He). cbn beta in *. lia.
- rewrite live_bytes_A2. unfold md1. pose proof (vm_backing_used_mmap a (Z_to_bv 64 len) md). rewrite len_u in *.
pose proof (lg_backing _ _ _ _ G). lia.
-   exact (lg_ceil _ _ _ _ G).
Qed.
Lemma ledger_x_A2 : ledger_x L1 A2 md1.
Proof.
pose proof grant_facts as (Hal & Hpos & Hceil & RF & Hbud). pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a).
assert (VM : vm_maps (m_vmmaps md1) = (a, Z_to_bv 64 len) :: vm_maps (m_vmmaps md)) by reflexivity.
split; rewrite ?VM.
- intros k rg x Hk Hl Hx. rewrite region_of_A2 in Hk. destruct (Nat.ltb_spec k r0).
+ rewrite (L1_old k rg Hk) in Hx. destruct (lx_cov _ _ _ X k rg x Hk Hl Hx) as (e & He & Hex). exists e. split; [right; exact He | exact Hex].
+ destruct (Nat.eqb_spec k r0); [|discriminate]. injection Hk as <-. subst k. rewrite L1_new in Hx. cbn [rgn reg_lo rg_kind rg_len] in Hx.
exists (a, Z_to_bv 64 len). split; [left; reflexivity|]. unfold iv_lo, iv_len. cbn [fst snd]. rewrite len_u. lia.
- intros e [<- | He]; [| exact (lx_maps _ _ _ X e He)]. unfold iv_lo, iv_len; cbn [fst snd]. rewrite len_u. lia.
- intros e1 e2 [<- | H1] [<- | H2].
+ left. reflexivity.
+ right. pose proof (new_disjoint_entry e2 H2). unfold iv_lo, iv_len in *; cbn [fst snd]. rewrite len_u. exact H0.
+ right. pose proof (new_disjoint_entry e1 H1) as D. unfold ranges_disjoint, iv_lo, iv_len in *; cbn [fst snd] in *. rewrite len_u. lia.
+ exact (lx_disj _ _ _ X e1 e2 H1 H2).
- intros k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2. rewrite region_of_A2 in H1, H2.
destruct (Nat.ltb_spec k1 r0); destruct (Nat.ltb_spec k2 r0).
+ rewrite (L1_old k1 rg1 H1), (L1_old k2 rg2 H2). exact (lx_regs _ _ _ X k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2).
+ destruct (Nat.eqb_spec k2 r0); [|discriminate]. injection H2 as <-. subst k2. rewrite (L1_old k1 rg1 H1), L1_new.
cbn [rgn reg_lo rg_kind rg_len] in *. unfold ranges_disjoint; cbn [fst snd].
pose proof (new_disjoint_region k1 rg1 (ly_reg L k1 + reg_lo rg1) H1 Hl1 ltac:(lia)).
pose proof (new_disjoint_region k1 rg1 (bv_unsigned a) H1 Hl1). pose proof (proj1 Hlen). lia.
+ destruct (Nat.eqb_spec k1 r0); [|discriminate]. injection H1 as <-. subst k1. rewrite (L1_old k2 rg2 H2), L1_new.
cbn [rgn reg_lo rg_kind rg_len] in *. unfold ranges_disjoint; cbn [fst snd].
pose proof (new_disjoint_region k2 rg2 (ly_reg L k2 + reg_lo rg2) H2 Hl2 ltac:(lia)).
pose proof (new_disjoint_region k2 rg2 (bv_unsigned a) H2 Hl2). pose proof (proj1 Hlen). lia.
+ destruct (Nat.eqb_spec k1 r0); [|discriminate]. destruct (Nat.eqb_spec k2 r0); [|discriminate]. exfalso. apply Hne. lia.
- intros e [<- | He].
+ exists r0, rgn. rewrite region_of_A2. rewrite Nat.ltb_irrefl, Nat.eqb_refl. split; [reflexivity|]. split; [reflexivity|].
rewrite L1_new. unfold iv_lo, iv_len; cbn [fst snd rgn rg_len]. rewrite len_u. lia.
+ destruct (lx_in _ _ _ X e He) as (k & rg & Hk & Hl & G1 & G2). exists k, rg.
rewrite region_of_A2. rewrite (proj2 (Nat.ltb_lt _ _) (region_of_A_lt k rg Hk)). rewrite (L1_old k rg Hk). auto.
- rewrite live_bytes_A2. cbn [State.live_bytes]. rewrite len_u. pose proof (lx_lb _ _ _ X). lia.
-
intros e He. change (vm_noaccess (m_vmmaps md1)) with (vm_noaccess (m_vmmaps md)) in He.
destruct (lx_noacc _ _ _ X e He) as (E & HE & G1 & G2 & HR). exists E. split; [right; exact HE|].
split; [exact G1|]. split; [exact G2|]. intros k rg Hk Hl Hkd Hp. rewrite region_of_A2 in Hk.
destruct (Nat.ltb_spec k r0).
+ rewrite (L1_old k rg Hk). exact (HR k rg Hk Hl Hkd Hp).
+ destruct (Nat.eqb_spec k r0); [|discriminate]. injection Hk as <-. subst k. rewrite L1_new. cbn [rgn rg_len].
pose proof (new_disjoint_entry E HE) as D. unfold ranges_disjoint in *; cbn [fst snd] in *. lia.
Qed.
Hypothesis PB : ptrs_below A.
Lemma loc_addr_below : forall l, (match l with LMem p => (prid p < r0)%nat | LCtx _ => True end) -> loc_addr L1 l = loc_addr L l.
Proof.
intros [o|[k o]] H; cbn; [reflexivity|]. cbn in H. unfold r0 in *.
destruct (Nat.eqb_spec k (length (st_regions A))); [lia | reflexivity].
Qed.
Lemma cell_mem_L1 : forall m c, refs_below r0 c -> cell_mem B L m c -> cell_mem B L1 m c.
Proof.
intros m [l w v] [H1 H2] H. unfold cell_mem in *. cbn [mc_loc mc_w mc_val] in *.
rewrite (loc_addr_below l H1). destruct v as [z|p|z|]; try exact H.
cbn [sval_num] in *. rewrite (loc_addr_below (LMem p) H2). exact H.
Qed.
Lemma crange_L1_old : forall rg, In rg (footprint A) -> crange L1 rg = crange L rg.
Proof.
intros rg Hin. unfold crange. f_equal. apply loc_addr_below.
destruct (In_footprint_inv A rg Hin) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst]; [exact I| |].
- destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & Hareas & _).
destruct (Hareas ar Har) as (k & o & r & -> & _ & _ & Hr & _). cbn. exact (region_of_A_lt k r Hr).
- cbn. exact (region_of_A_lt k r Hr).
Qed.
Lemma footprint_pos : forall rg, In rg (footprint A) -> 0 < snd rg.
Proof.
intros rg Hin.
destruct (In_footprint_inv A rg Hin) as [-> | [(ar & Har & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [snd]; unfold CTX_SIZE, PGSZ; try lia.
pose proof (lg_maps _ _ _ _ G k r Hr Hl ltac:(rewrite Hk; discriminate)) as Hin2.
destruct (lx_maps _ _ _ X _ Hin2) as [P _]. unfold iv_len in P. cbn [snd] in P. unfold w64 in P.
pose proof (lg_placed _ _ _ _ G k r Hr Hl) as (_ & Hlo & Hhi & _). pose proof (proj1 alloc_ceiling_val).
destruct (Z_lt_le_dec 0 (rg_len r)); [lia|].
destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & _ & _ & _ & _ & _ & _ & _ & Hnn).
pose proof (Hnn k r Hr). assert (E0 : rg_len r = 0) by lia. rewrite E0 in P. change (bv_unsigned (Z_to_bv 64 0)) with 0 in P. lia.
Qed.
Lemma layout_ok_A2 : layout_ok L1 A2.
Proof.
pose proof grant_facts as (Hal & Hpos & Hceil & RF & Hbud). pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a).
pose proof (mc_layout _ _ _ _ _ M) as (Y1 & Y2 & Y3 & Y4).
split; [exact Y1|]. split; [|split].
- intros k rg Hk Hl. rewrite region_of_A2 in Hk. destruct (Nat.ltb_spec k r0).
+ rewrite (L1_old k rg Hk). exact (Y2 k rg Hk Hl).
+ destruct (Nat.eqb_spec k r0); [|discriminate]. subst k. rewrite L1_new. exact Hal.
- rewrite footprint_A2, map_app. cbn [map]. apply pairwise_app.
+ rewrite (map_ext_in _ _ _ crange_L1_old). exact Y3.
+ cbn. split; [intros y [] | exact I].
+ intros x y Hx [<-|[]]. apply in_map_iff in Hx as (rg & <- & Hrg). rewrite (crange_L1_old rg Hrg).
unfold ranges_disjoint, crange. cbn [fst snd loc_addr]. rewrite L1_new.
pose proof (footprint_pos rg Hrg).
pose proof (new_disjoint_footprint rg (loc_addr L (fst rg)) Hrg ltac:(lia)).
pose proof (new_disjoint_footprint rg (bv_unsigned a) Hrg). pose proof (proj1 Hlen). lia.
- rewrite footprint_A2. intros rg Hin. apply in_app_iff in Hin as [Hin | [<- | []]].
+ rewrite (crange_L1_old rg Hin). exact (Y4 rg Hin).
+ unfold crange. cbn [fst snd loc_addr]. rewrite L1_new, Z.add_0_r. lia.
Qed.
Definition ctxw (x : Z) : Prop :=
(ms_ctx B + 12 <= x < ms_ctx B + 16) \/ (ms_ctx B + 848 <= x < ms_ctx B + 880) \/ x = ms_ctx B + 912.
Section i.
Variable mem5 : word -> option byte.
Variable W : Z -> Prop.
Hypothesis AG : forall x, 0 <= x < 2 ^ 64 -> ~ W x -> ~ (bv_unsigned a <= x < bv_unsigned a + len) -> mem5 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Hypothesis WO : forall x, W x -> (in_footprint L A x \/ static_owned B x) -> ctxw x.
Hypothesis ZP : forall x, bv_unsigned a <= x < bv_unsigned a + len -> present mem5 x.
Hypothesis CTR : forall k, (k < 4)%nat -> mbyte (ms_segs B) mem5 (ms_ctx B + 12 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (st_mmap_counter A) 4 k)).
Hypothesis SEQ : mbyte (ms_segs B) mem5 (ms_ctx B + 912) = Some (Z_to_bv 8 (le_byte (st_seq A2) 1 0)).
Hypothesis USEQ : forall k, (k < 32)%nat -> mbyte (ms_segs B) mem5 (ms_ctx B + 848 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (nth k (st_unmap_seq A2) 0) 1 0)).
Lemma old_byte : forall x, in_footprint L A x -> ~ ctxw x -> mem5 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof.
intros x Hfp Hn. pose proof (proj1 alloc_ceiling_val). destruct Hfp as (rg & Hrg & Hx).
pose proof (footprint_low B L A mem md rg x M Hrg Hx).
apply AG; [lia | intros HW; apply Hn; apply WO; [exact HW | left; exists rg; auto] | exact (new_disjoint_footprint rg x Hrg Hx)].
Qed.
Lemma old_static : forall x, static_owned B x -> ~ ctxw x -> mem5 (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof.
intros x Hs Hn. pose proof (so_img_hi _ (mc_syms _ _ _ _ _ M) x (so_statics_img _ (mc_syms _ _ _ _ _ M) x Hs)).
pose proof (proj1 alloc_ceiling_val).
apply AG; [lia | intros HW; apply Hn; apply WO; [exact HW | right; exact Hs] |].
apply new_disjoint_img. apply (so_statics_img _ (mc_syms _ _ _ _ _ M)). exact Hs.
Qed.
Lemma old_cell : forall c, In c (image A) \/ In c (tail_cells A) ->
(forall k, (k < mc_w c)%nat -> ~ ctxw (loc_addr L (mc_loc c) + Z.of_nat k)) ->
cell_mem B L1 mem5 c.
Proof.
intros c Hc Hnw. apply cell_mem_L1; [apply PB; exact Hc|].
assert (OWN : forall k, (k < mc_w c)%nat -> in_footprint L A (loc_addr L (mc_loc c) + Z.of_nat k)).
{ intros k Hk. destruct Hc as [Hc|Hc].
- exact (proj1 (image_cell_owned L A c k (mc_wf _ _ _ _ _ M) (mc_layout _ _ _ _ _ M) Hc Hk)).
- exact (proj1 (proj1 (Forall_forall _ _) (mc_tail_geom _ _ _ _ _ M) c Hc k Hk)). }
assert (H : cell_mem B L mem c).
{ destruct Hc as [Hc|Hc]; [exact (memrep_cell B L A mem c (MRc_memrep B L A mem md M) Hc) | exact (memrep_tail B L A mem c (MRc_memrep B L A mem md M) Hc)]. }
unfold cell_mem in *. destruct c as [l w v]; cbn [mc_loc mc_w mc_val] in *.
destruct v as [z|p|z|];
try (intros k Hk; unfold mbyte; rewrite (old_byte _ (OWN k Hk) (Hnw k Hk)); apply H; exact Hk).
intros Hw. destruct (H Hw) as (b & Hb & Hz). exists b. split; [|exact Hz].
unfold mbyte in *. specialize (OWN 0%nat Hw). specialize (Hnw 0%nat Hw). rewrite Z.add_0_r in OWN, Hnw.
rewrite (old_byte _ OWN Hnw). exact Hb.
Qed.
Lemma rest_cell_off_img : forall c k, In c (areas_cells A (st_areas A) ++ flat_map (fun gm => group_cells (fst gm) (snd gm)) (used_metas A)) ->
(k < mc_w c)%nat -> ~ in_img B (loc_addr L (mc_loc c) + Z.of_nat k).
Proof.
intros c k Hin Hk. pose proof (mc_wf _ _ _ _ _ M) as HW.
apply in_app_iff in Hin as [Hin | Hin].
- apply In_areas_cells in Hin as (ar & next & Har & Hc).
destruct (In_area_cells A ar next c Hc) as (d & El & Hd1 & Hd2). rewrite El.
destruct (inv_areas HW) as (_ & Hareas & _).
destruct (Hareas ar Har) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen2 & _). cbn [loc_addr padd].
destruct (lg_placed _ _ _ _ G r rg Hr Hl) as (_ & _ & _ & Himg). apply Himg. unfold PGSZ in *. lia.
- apply in_flat_map in Hin as ([g am] & Hg & Hc). cbn [fst snd] in Hc.
apply (used_metas_usedX A g am HW) in Hg as Hu.
destruct (In_group_cells_span [] None U0 A g am c HW Hu Hc) as (d & El & Hd1 & Hd2). rewrite El.
apply (used_metas_usedX A g am HW) in Hu.
destruct (group_in_mapping A g am HW Hu) as (r & o & rg & Emem & Hr & Hk2 & Hl & Ho & Hext & _).
rewrite Emem. cbn [loc_addr padd].
destruct (lg_placed _ _ _ _ G r rg Hr Hl) as (_ & _ & _ & Himg). apply Himg. lia.
Qed.
Lemma ctxw_img : forall x, ctxw x -> in_img B x.
Proof.
intros x Hx. apply (so_ctx_img _ (mc_syms _ _ _ _ _ M)). unfold ctxw, CTX_SIZE in *. lia.
Qed.
Hypothesis TIR : forall c k, In c (tail_cells A) -> (k < mc_w c)%nat -> ~ in_img B (loc_addr L (mc_loc c) + Z.of_nat k).
Lemma In_ctx_cells_cases : forall s c, In c (ctx_cells s) ->
In c [MCell (LCtx CTX_secret) 8 (if st_init_done s then VSec else VZ 0);
MCell (LCtx CTX_init_done) 4 (VZ (if st_init_done s then 1 else 0));
MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter s));
MCell (LCtx CTX_free_meta_head) 8 (optr (st_free_meta_head s));
MCell (LCtx CTX_avail_meta) 8 (match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end);
MCell (LCtx CTX_avail_meta_count) 8 (VZ (st_avail_meta_count s));
MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s));
MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s));
MCell (LCtx CTX_meta_area_head) 8 (optr (st_area_head s));
MCell (LCtx CTX_meta_area_tail) 8 (optr (st_area_tail s));
MCell (LCtx CTX_avail_meta_areas) 8
(if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0)
then VZ 0 else VP (st_avail_meta_areas s));
MCell (LCtx CTX_seq) 1 (VZ (st_seq s));
MCell (LCtx CTX_brk) 8 (match st_brk s with BrkNever => VZ 0 | BrkDead => VZ (-1) | BrkCur r p => VP (SP r (PGSZ * p)) end)]
\/ (exists k, (k < 48)%nat /\ c = MCell (LCtx (CTX_active + 8 * Z.of_nat k)) 8 (optr (nth k (st_active s) None)))
\/ (exists k, (k < 48)%nat /\ c = MCell (LCtx (CTX_usage + 8 * Z.of_nat k)) 8 (VZ (nth k (st_usage s) 0)))
\/ (exists k, (k < 32)%nat /\ c = MCell (LCtx (CTX_unmap_seq + Z.of_nat k)) 1 (VZ (nth k (st_unmap_seq s) 0)))
\/ (exists k, (k < 32)%nat /\ c = MCell (LCtx (CTX_bounces + Z.of_nat k)) 1 (VZ (nth k (st_bounces s) 0))).
Proof.
intros s c H. unfold ctx_cells in H. rewrite !in_app_iff in H.
destruct H as [H|[H|[H|[H|H]]]]; [left; exact H | right; left | right; right; left | right; right; right; left | right; right; right; right];
apply in_map_iff in H as (k & <- & Hk); apply in_seq in Hk; exists k; (split; [lia | reflexivity]).
Qed.
Lemma ctx_loc : forall off, loc_addr L1 (LCtx off) = ms_ctx B + off.
Proof. intros off. cbn. rewrite (mc_ctx _ _ _ _ _ M). reflexivity. Qed.
Theorem memrep_A2 : memrep B L1 A2 mem5.
Proof using All.
pose proof (mc_ctx _ _ _ _ _ M) as EC. pose proof (mc_wf _ _ _ _ _ M) as HW.
assert (OLDI : forall c, In c (areas_cells A (st_areas A) ++ flat_map (fun gm => group_cells (fst gm) (snd gm)) (used_metas A)) ->
cell_mem B L1 mem5 c).
{ intros c Hc. apply old_cell; [left; rewrite image_A; apply in_app_iff; right; exact Hc|].
intros k Hk Hw. exact (rest_cell_off_img c k Hc Hk (ctxw_img _ Hw)). }
assert (OLDC : forall c, In c (ctx_cells A) -> (forall k, (k < mc_w c)%nat -> ~ ctxw (loc_addr L (mc_loc c) + Z.of_nat k)) -> cell_mem B L1 mem5 c).
{ intros c Hc Hnw. apply old_cell; [left; rewrite image_A; apply in_app_iff; left; exact Hc | exact Hnw]. }
split; [| split].
- rewrite image_A2. apply Forall_app. split; [| apply Forall_forall; exact OLDI].
apply Forall_forall. intros c Hc.
assert (E2 : st_init_done A2 = st_init_done A /\ st_mmap_counter A2 = st_mmap_counter A /\ st_free_meta_head A2 = st_free_meta_head A /\
st_areas A2 = st_areas A /\ st_avail_meta A2 = st_avail_meta A /\ st_avail_meta_count A2 = st_avail_meta_count A /\
st_avail_meta_area_count A2 = st_avail_meta_area_count A /\ st_meta_alloc_shift A2 = st_meta_alloc_shift A /\
st_area_head A2 = st_area_head A /\ st_area_tail A2 = st_area_tail A /\ st_avail_meta_areas A2 = st_avail_meta_areas A /\
st_brk A2 = st_brk A /\ st_active A2 = st_active A /\ st_usage A2 = st_usage A /\ st_bounces A2 = st_bounces A).
{ unfold A2, seqf, A1. destruct (st_seq _ =? 255); repeat split; reflexivity. }
destruct E2 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15).
destruct (In_ctx_cells_cases A2 c Hc) as [H13 | [(k & Hk & ->) | [(k & Hk & ->) | [(k & Hk & ->) | (k & Hk & ->)]]]].
+ rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12 in H13. cbn [In] in H13.
destruct H13 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
try (apply OLDC; [unfold ctx_cells; apply in_app_iff; left; cbn; tauto
| intros j Hj; cbn [mc_loc mc_w loc_addr] in Hj |- *; rewrite EC; unfold ctxw;
unfold CTX_secret, CTX_init_done, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count,
CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_brk; lia]).
*   unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. intros j Hj. rewrite ctx_loc. unfold CTX_mmap_counter. apply CTR. exact Hj.
*   unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. intros j Hj. rewrite ctx_loc. unfold CTX_seq.
destruct j; [|lia]. rewrite Z.add_0_r. exact SEQ.
+ rewrite E13. apply OLDC; [unfold ctx_cells; rewrite !in_app_iff; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
intros j Hj. cbn [mc_loc mc_w loc_addr] in Hj |- *. rewrite EC. unfold ctxw, CTX_active. lia.
+ rewrite E14. apply OLDC; [unfold ctx_cells; rewrite !in_app_iff; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
intros j Hj. cbn [mc_loc mc_w loc_addr] in Hj |- *. rewrite EC. unfold ctxw, CTX_usage. lia.
+   unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. intros j Hj. rewrite ctx_loc. unfold CTX_unmap_seq.
destruct j; [|lia]. rewrite Z.add_0_r. replace (ms_ctx B + (848 + Z.of_nat k)) with (ms_ctx B + 848 + Z.of_nat k) by lia. apply USEQ. exact Hk.
+ rewrite E15. apply OLDC; [unfold ctx_cells; rewrite !in_app_iff; right; right; right; right; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
intros j Hj. cbn [mc_loc mc_w loc_addr] in Hj |- *. rewrite EC. unfold ctxw, CTX_bounces. lia.
- rewrite tail_cells_A2. apply Forall_forall. intros c Hc. apply old_cell; [right; exact Hc|].
intros k Hk Hw. exact (TIR c k Hc Hk (ctxw_img _ Hw)).
- rewrite footprint_A2. apply Forall_app. split.
+ apply Forall_forall. intros rg Hrg. unfold foot_ok. destruct rg as [[o|p] n]; cbn [fst snd]; [exact I|].
intros x Hx.
assert (El : loc_addr L1 (LMem p) = loc_addr L (LMem p)).
{ pose proof (crange_L1_old _ Hrg) as Ec. unfold crange in Ec. cbn [fst snd] in Ec. congruence. }
rewrite El in Hx.
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ M) _ Hrg) as F. cbn [foot_ok fst snd] in F.
destruct (F x Hx) as [b Hb]. exists b. pose proof (footprint_low B L A mem md _ x M Hrg Hx).
rewrite (old_byte x); [exact Hb | exists (LMem p, n); auto |].
intros Hw. destruct (In_footprint_inv A _ Hrg) as [E0 | [(ar & Har & E0) | (k & r & Hr & Hk & Hl & E0)]]; try discriminate;
injection E0 as E0p E0n; subst; cbn [loc_addr] in Hx.
* destruct (inv_areas HW) as (_ & Hareas & _). destruct (Hareas ar Har) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen2 & _).
cbn [loc_addr] in Hx. destruct (lg_placed _ _ _ _ G r rg Hr Hl) as (_ & _ & _ & Himg).
apply (Himg x); [assert (PGSZ = 4096) by reflexivity; lia | apply ctxw_img; exact Hw].
* destruct (lg_placed _ _ _ _ G k r Hr Hl) as (_ & _ & _ & Himg). apply (Himg x); [lia | apply ctxw_img; exact Hw].
+ apply Forall_cons; [|apply Forall_nil]. unfold foot_ok. cbn [fst snd loc_addr]. rewrite L1_new, Z.add_0_r. exact ZP.
Qed.
Hypothesis SNC : forall x, static_owned B x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Lemma statics_A2 : statics_ok B mem5.
Proof.
pose proof (mc_statics _ _ _ _ _ M) as ST. pose proof (so_ctx_lo _ (mc_syms _ _ _ _ _ M)).
assert (SO : forall x, static_owned B x -> ~ ctxw x -> mbyte (ms_segs B) mem5 x = mbyte (ms_segs B) mem x).
{ intros x Hs Hn. unfold mbyte. rewrite (old_static x Hs Hn). reflexivity. }
assert (NC : forall x, static_owned B x -> ~ ctxw x).
{ intros x Hs Hw. apply (SNC x Hs). unfold ctxw, CTX_SIZE in *. lia. }
split.
- rewrite SO; [apply (st_needlocks _ _ ST) | unfold static_owned; lia | apply NC; unfold static_owned; lia].
- intros k Hk. rewrite SO; [apply (st_pagesize _ _ ST); exact Hk | unfold static_owned; lia | apply NC; unfold static_owned; lia].
- intros k Hk. rewrite SO; [apply (st_lock _ _ ST); exact Hk | unfold static_owned; lia | apply NC; unfold static_owned; lia].
- intros k Hk. rewrite SO; [apply (st_got _ _ ST); exact Hk | unfold static_owned; lia | apply NC; unfold static_owned; lia].
- destruct (st_guard _ _ ST) as [g Hg]. exists g. intros k Hk. rewrite SO; [apply Hg; exact Hk | unfold static_owned; lia | apply NC; unfold static_owned; lia].
- intros x Hx. rewrite SO; [apply (st_tables _ _ ST); exact Hx | unfold static_owned; unfold table_addr in Hx; lia | apply NC; unfold static_owned; unfold table_addr in Hx; lia].
Qed.
Lemma tail_geom_A2 : tail_geom L1 A2.
Proof.
unfold tail_geom. rewrite tail_cells_A2. apply Forall_forall. intros c Hc k Hk.
pose proof (proj1 (Forall_forall _ _) (mc_tail_geom _ _ _ _ _ M) c Hc k Hk) as [(rg & Hrg & Hx) Hnb]. cbn beta in *.
pose proof (PB c (or_intror Hc)) as [Hl _].
rewrite (loc_addr_below (mc_loc c) Hl). split.
- exists rg. rewrite footprint_A2. split; [apply in_app_iff; left; exact Hrg|].
pose proof (crange_L1_old rg Hrg) as Ec. unfold crange in Ec. injection Ec as Ec1. rewrite Ec1. exact Hx.
- intros (b & Hb & Hbx). apply Hnb. exists b. rewrite user_blocks_A2 in Hb. split; [exact Hb|].
destruct b as [q m]. cbn [fst snd] in *.
assert (Hq : (prid q < r0)%nat).
{ destruct (block_region A q m (mc_wf _ _ _ _ _ M) Hb) as (kk & o & rg2 & -> & Hr2 & _). cbn. exact (region_of_A_lt kk rg2 Hr2). }
rewrite (loc_addr_below (LMem q) Hq) in Hbx. exact Hbx.
Qed.
Lemma Inv_A2 : forall Xs R U, Inv Xs R U A -> Inv Xs R U A2.
Proof.
intros Xs R U HI. unfold A2, seqf, A1.
pose proof (Inv_new_map Xs R U A len HI ltac:(lia)) as HI1. fold rgn in HI1.
pose proof (inv_ctx HI1) as (_&_&_&_&_&_&_&C8&_).
destruct (st_seq (set_regions (st_regions A ++ [rgn]) A) =? 255) eqn:E.
- apply Inv_set_seq; [|lia]. destruct repeat0_32_range as [R1 R2]. apply Inv_set_unmap_seq; [exact HI1 | exact R1 | exact R2].
- apply Z.eqb_neq in E. apply Inv_set_seq; [exact HI1 | cbn in *; lia].
Qed.
Theorem midrep_after_seq : midrep B L1 A2 mem5 md1.
Proof.
destruct (mc_md _ _ _ _ _ M) as (H1 & H2 & H3).
split.
- exact (mc_syms _ _ _ _ _ M).
- exact memrep_A2.
- exact tail_geom_A2.
- exact statics_A2.
- exact ledger_ok_A2.
- exact ledger_x_A2.
- exact layout_ok_A2.
- cbn. exact (mc_ctx _ _ _ _ _ M).
- cbn. exact (mc_sec _ _ _ _ _ M).
- unfold md1. rewrite mmap_model_halted. split; [exact H1|]. split; [exact (eq_trans (mmap_model_lazy _ _ _) H2) | exact H3].
Qed.
End i.
End D1.
End h.
