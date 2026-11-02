(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and numbers changed; 1 of its 535 lines of code are new or changed and 2 lines of the source are left out. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition w64 (z : Z) : word := Z_to_bv 64 z.
End d.
Notation in_img := YO0d.in_img (only parsing).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition in_img_unfold (B : malloc_syms) (a : Z) : in_img B a = (ms_segs B <> [] /\ exists s, In s (segments_reserved (ms_segs B)) /\
bv_unsigned (fst s) <= a < bv_unsigned (fst s) + bv_unsigned (snd s)) := eq_refl.
Record syms_ok (B : malloc_syms) : Prop := {
so_ctx_al : ms_ctx B mod 8 = 0;
so_ctx_lo : 4096 <= ms_ctx B;
so_ctx_hi : ms_ctx B + CTX_SIZE <= alloc_ceiling;
so_rtop : 4096 <= reserved_top (segments_reserved (ms_segs B));
so_ctx_rw : forall mem a, ms_ctx B <= a < ms_ctx B + CTX_SIZE ->
writable_at (ms_segs B) mem a /\ exists b, mbyte (ms_segs B) mem a = Some b;
so_ctx_img : forall a, ms_ctx B <= a < ms_ctx B + CTX_SIZE -> in_img B a;
so_statics_img : forall a, static_owned B a -> in_img B a;
so_img_hi : forall a, in_img B a -> 0 <= a < alloc_ceiling;
so_size_classes : forall k, (k < 48)%nat ->
exists lo hi, seg_rom (ms_segs B) (w64 (ms_size_classes B + 2 * Z.of_nat k)) = Some lo /\
seg_rom (ms_segs B) (w64 (ms_size_classes B + 2 * Z.of_nat k + 1)) = Some hi /\
bv_unsigned lo + 256 * bv_unsigned hi = nth k size_classes 0;
so_small_cnt : forall r c, (r < 9)%nat -> (c < 3)%nat ->
exists b, seg_rom (ms_segs B) (w64 (ms_small_cnt B + Z.of_nat (3 * r + c))) = Some b /\
bv_unsigned b = nth c (nth r small_cnt_tab []) 0;
so_med_cnt : forall c, (c < 4)%nat ->
exists b, seg_rom (ms_segs B) (w64 (ms_med_cnt B + Z.of_nat c)) = Some b /\ bv_unsigned b = nth c med_cnt_tab 0;
so_debruijn : forall k, 0 <= k < 32 ->
exists b, seg_rom (ms_segs B) (w64 (ms_debruijn B + (Z.shiftr ((2 ^ k * 125613361) mod 2 ^ 32) 27))) = Some b /\
bv_unsigned b = k
}.
Section f.
Variable B : malloc_syms.
Let segs := ms_segs B.
Definition cell_mem (L : layout) (mem : word -> option byte) (c : mcell) : Prop :=
let a := loc_addr L (mc_loc c) in
match mc_val c with
| VLo5 z => (0 < mc_w c)%nat -> exists b, mbyte segs mem a = Some b /\ bv_unsigned b mod 32 = z
| v => forall k, (k < mc_w c)%nat ->
mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (sval_num L v) (mc_w c) k))
end.
Definition slot_end (am : ameta) (i : Z) : sptr := padd (slot_start am i) (stride_of am - IB).
Definition reserved_of (am : ameta) (fr : frame) : Z := stride_of am - IB - UNIT * fr_off fr - fr_n fr.
Definition frame_tail_cells (am : ameta) (i : Z) : list mcell :=
match ss_fr (nth_slot am i) with
| Some fr =>
match fr_kind fr with
| FUser =>
(if 0 <? reserved_of am fr then [MCell (LMem (padd (frame_ptr am i fr) (fr_n fr))) 1 (VZ 0)] else [])
++ (if 5 <=? reserved_of am fr
then [MCell (LMem (padd (slot_end am i) (-4))) 4 (VZ (reserved_of am fr));
MCell (LMem (padd (slot_end am i) (-5))) 1 (VZ 0)]
else [])
| FGroup => []
end
| None => []
end.
Definition group_tail_cells (am : ameta) : list mcell :=
MCell (LMem (padd (am_mem am) (group_extent am))) 1 (VZ 0)
:: flat_map (frame_tail_cells am) (zseq 0 (am_last am + 1)).
Definition tail_cells (A : astate) : list mcell :=
flat_map (fun gm : sptr * ameta => group_tail_cells (snd gm)) (used_metas A).
Definition tail_geom (L : layout) (A : astate) : Prop :=
Forall (fun c => forall k, (k < mc_w c)%nat -> alloc_owned L A (loc_addr L (mc_loc c) + Z.of_nat k)) (tail_cells A).
Definition foot_ok (L : layout) (mem : word -> option byte) (rg : loc * Z) : Prop :=
match fst rg with
| LCtx _ => True
| LMem _ => forall x, loc_addr L (fst rg) <= x < loc_addr L (fst rg) + snd rg -> present mem x
end.
Definition table_addr (a : Z) : Prop :=
(ms_debruijn B - 108 <= a < ms_debruijn B + 32) \/ (ms_size_classes B <= a < ms_size_classes B + 96) \/
(ms_small_cnt B <= a < ms_small_cnt B + 27) \/ (ms_med_cnt B <= a < ms_med_cnt B + 4).
Record statics_ok (mem : word -> option byte) : Prop := {
st_needlocks : mbyte segs mem (ms_libc B + 3) = Some (Z_to_bv 8 0);
st_pagesize : word_mem segs mem (ms_libc B + 48) 4096;
st_lock : forall k, (k < 4)%nat -> mbyte segs mem (ms_lock B + Z.of_nat k) = Some (Z_to_bv 8 0);
st_got : word_mem segs mem (ms_got_guard B) (ms_guard B);
st_guard : exists g, word_mem segs mem (ms_guard B) g;
st_tables : forall a, table_addr a -> mbyte segs mem a = seg_rom segs (w64 a)
}.
Record ledger_ok (L : layout) (A : astate) (md : Model) : Prop := {
lg_reserved : vm_reserved (m_vmmaps md) = segments_reserved segs;
lg_limit : SRC_LIM_MIN <= vm_limit (m_vmmaps md);
lg_maps : forall r rg, region_of A r = Some rg -> rg_live rg = true -> rg_kind rg <> RkBrk ->
In (w64 (ly_reg L r), w64 (rg_len rg)) (vm_maps (m_vmmaps md));
lg_noaccess : forall r rg off, region_of A r = Some rg -> rg_live rg = true -> rg_kind rg = RkMetaRes ->
0 <= off -> off + PGSZ <= rg_len rg -> off mod PGSZ = 0 -> ~ In off (rg_rw rg) ->
map_contains (vm_noaccess (m_vmmaps md)) (w64 (ly_reg L r + off)) (w64 PGSZ) = true /\
map_contains (vm_maps (m_vmmaps md)) (w64 (ly_reg L r + off)) (w64 PGSZ) = true;
lg_brk0 : ly_brk0 L mod PGSZ = 0 /\ 4096 <= ly_brk0 L /\ ly_brk0 L + 2 * PGSZ <= alloc_ceiling /\
bv_unsigned (vm_start_brk (m_vmmaps md)) <= ly_brk0 L /\
reserved_top (segments_reserved segs) <= ly_brk0 L;
lg_brk : match st_brk A with
| BrkNever => bv_unsigned (vm_brk (m_vmmaps md)) = ly_brk0 L
| BrkCur r p => bv_unsigned (vm_brk (m_vmmaps md)) = ly_reg L r + PGSZ * p /\ ly_reg L r = ly_brk0 L
| BrkDead => True
end;
lg_placed : forall r rg, region_of A r = Some rg -> rg_live rg = true ->
ly_reg L r mod PGSZ = 0 /\ 4096 <= ly_reg L r /\ ly_reg L r + rg_len rg <= alloc_ceiling /\
(forall a, ly_reg L r <= a < ly_reg L r + rg_len rg -> ~ in_img B a);
lg_count : Z.of_nat (length (vm_maps (m_vmmaps md))) <= nslots A;
lg_sizes : Forall (fun p => bv_unsigned (snd p) <= live_bytes A) (vm_maps (m_vmmaps md));
lg_backing : vm_backing_used md <= live_bytes A;
lg_ceil : YM05.ceil_of_top (alloc_top (m_vmmaps md))
}.
Record MRc (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop := {
mc_syms : syms_ok B;
mc_wf : WF A;
mc_bounded : bounded A;
mc_layout : layout_ok L A;
mc_ctx : ly_ctx L = ms_ctx B;
mc_sec : 0 <= ly_sec L < 2 ^ 64;
mc_cells : Forall (cell_mem L mem) (image A);
mc_tail : Forall (cell_mem L mem) (tail_cells A);
mc_tail_geom : tail_geom L A;
mc_foot : Forall (foot_ok L mem) (footprint A);
mc_statics : statics_ok mem;
mc_ledger : ledger_ok L A md;
mc_md : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = []
}.
End f.
Section h.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma image_cell_owned : forall L A c k,
WF A -> layout_ok L A -> In c (image A) -> (k < mc_w c)%nat ->
alloc_owned L A (loc_addr L (mc_loc c) + Z.of_nat k).
Proof.
intros L A c k HW HL Hin Hk. split.
- destruct (image_in_footprint A L c HW HL Hin) as (rg & Hrg & [H1 H2]).
exists rg. split; [exact Hrg|]. unfold cell_range, crange in *. cbn [fst snd] in *. lia.
- intros (b & Hb & Hx).
pose proof (image_outside_user_blocks A L c b HW HL Hin Hb) as HD.
unfold ranges_disjoint, cell_range, block_range in HD. cbn [fst snd] in HD. lia.
Qed.
Lemma block_region : forall A p n,
WF A -> In (p, n) (user_blocks A) ->
exists k o rg, p = SP k o /\ region_of A k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= o /\ 0 <= n /\ o + n <= rg_len rg /\ o mod 16 = 0.
Proof.
intros A p n HW Hin.
destruct (user_blocks_frame A p n HW Hin) as (g & am & idx & fr & Hu & Hidx & Hfr & Hk & Hn & ->).
pose proof (proj2 (used_metas_usedX A g am HW) Hu) as Hum.
destruct (group_in_mapping A g am HW Hum) as (k & o & rg & Emem & Hrg & Hkind & Hlive & Ho & Hext & _).
pose proof (inv_groups HW g am Hu) as G.
pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((Glast & _) & _ & Gsl & _).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
pose proof (stride_mod16 _ _ _ _ _ _ HW Hu) as Hs16.
pose proof (used_group_aligned [] None U0 A HW _ g am Hu (Nat.le_refl _)) as Ha16.
exists k, (o + UNIT + stride_of am * idx + UNIT * fr_off fr), rg.
unfold frame_ptr, slot_start. rewrite Emem. cbn [padd]. subst n.
split; [f_equal; lia|]. split; [exact Hrg|]. split; [exact Hkind|]. split; [exact Hlive|].
unfold group_extent, UNIT, IB in *. rewrite Emem in Ha16. cbn [poff] in Ha16.
assert (Hsi : stride_of am * idx <= stride_of am * am_last am) by (apply Z.mul_le_mono_nonneg_l; lia).
split; [nia|]. split; [lia|]. split; [nia|].
replace (o + 16 + stride_of am * idx + 16 * fr_off fr) with (o + stride_of am * idx + (1 + fr_off fr) * 16) by lia.
rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia.
rewrite Z.add_mod, Ha16, Z.add_0_l, Z.mod_mod by lia.
rewrite Z.mul_mod, Hs16, Z.mul_0_l, Z.mod_0_l by lia. reflexivity.
Qed.
Lemma map_region_in_footprint : forall A k rg,
region_of A k = Some rg -> rg_kind rg = RkMap -> rg_live rg = true ->
In (LMem (SP k 0), rg_len rg) (footprint A).
Proof.
intros A k rg Hrg Hkind Hlive. unfold footprint. right. apply in_app_iff. right.
apply in_flat_map. exists k. split.
- apply in_seq. unfold region_of in Hrg. split; [lia|]. cbn.
destruct (Nat.lt_ge_cases k (length (st_regions A))) as [H|H]; [exact H|].
rewrite (proj2 (nth_error_None _ _) H) in Hrg. discriminate.
- rewrite Hrg, Hkind, Hlive. left. reflexivity.
Qed.
Lemma In_footprint_inv : forall A rg,
In rg (footprint A) ->
rg = (LCtx 0, CTX_SIZE) \/
(exists a, In a (st_areas A) /\ rg = (LMem a, PGSZ)) \/
(exists k r, region_of A k = Some r /\ rg_kind r = RkMap /\ rg_live r = true /\ rg = (LMem (SP k 0), rg_len r)).
Proof.
intros A rg Hin. unfold footprint in Hin. destruct Hin as [<- | Hin]; [left; reflexivity|].
apply in_app_iff in Hin as [Hin | Hin].
- right; left. apply in_map_iff in Hin as (a & <- & Ha). exists a. auto.
- right; right. apply in_flat_map in Hin as (k & _ & Hk).
destruct (region_of A k) as [r|] eqn:Hr; [|destruct Hk].
destruct (rg_kind r) eqn:Hkd; try (destruct Hk; fail).
destruct (rg_live r) eqn:Hl; [|destruct Hk]. destruct Hk as [<- | []].
exists k, r. auto.
Qed.
Lemma footprint_low : forall L A mem md rg x,
MRc B L A mem md -> In rg (footprint A) ->
loc_addr L (fst rg) <= x < loc_addr L (fst rg) + snd rg -> 4096 <= x < alloc_ceiling.
Proof.
intros L A mem md rg x M Hin Hx.
destruct (In_footprint_inv A rg Hin) as [-> | [(a & Ha & ->) | (k & r & Hr & Hk & Hl & ->)]]; cbn [fst snd loc_addr] in Hx.
- rewrite (mc_ctx _ _ _ _ _ M) in Hx. pose proof (so_ctx_lo _ (mc_syms _ _ _ _ _ M)). pose proof (so_ctx_hi _ (mc_syms _ _ _ _ _ M)). lia.
- destruct (inv_areas (mc_wf _ _ _ _ _ M)) as (_ & Hareas & _).
destruct (Hareas a Ha) as (r & o & rg & -> & _ & Ho & Hr & Hl & Hlen & _). cbn [loc_addr] in Hx.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) r rg Hr Hl) as (_ & H1 & H2 & _). unfold PGSZ in *. lia.
- destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k r Hr Hl) as (_ & H1 & H2 & _). lia.
Qed.
Lemma owned_low : forall L A mem md a, MRc B L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling.
Proof.
intros L A mem md a M [[(rg & Hrg & Hx) _] | Hs].
- pose proof (footprint_low L A mem md rg a M Hrg Hx). lia.
- apply (so_img_hi _ (mc_syms _ _ _ _ _ M)). apply (so_statics_img _ (mc_syms _ _ _ _ _ M)). exact Hs.
Qed.
Lemma blocks_facts : forall L A mem md p n i,
MRc B L A mem md -> In (p, n) (user_blocks A) -> 0 <= i < n ->
present mem (ptr_addr L p + i) /\ 4096 <= ptr_addr L p /\ ptr_addr L p + n <= alloc_ceiling /\
~ owned B L A (ptr_addr L p + i).
Proof.
intros L A mem md p n i M Hin Hi.
destruct (block_region A p n (mc_wf _ _ _ _ _ M) Hin) as (k & o & rg & -> & Hrg & Hkind & Hlive & Ho & Hn & Hlen & _).
unfold ptr_addr. cbn [loc_addr].
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k rg Hrg Hlive) as (Hal & H1 & H2 & Himg).
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ M) _ (footprint_region_In A k rg Hrg Hkind Hlive)) as Hf.
cbn [foot_ok fst snd loc_addr] in Hf.
split; [apply Hf; lia|]. split; [lia|]. split; [lia|].
intros [[_ Hnb] | Hs].
- apply Hnb. exists (SP k o, n). split; [exact Hin|]. cbn [fst snd loc_addr]. lia.
- apply (Himg (ly_reg L k + o + i)); [lia|]. apply (so_statics_img _ (mc_syms _ _ _ _ _ M)). exact Hs.
Qed.
Lemma vm_backing_used_ext : forall md md',
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md ->
vm_backing_used md' = vm_backing_used md.
Proof. intros md md' H1 H2 H3. unfold vm_backing_used. rewrite H1, H2, H3. reflexivity. Qed.
Lemma in_block_dec : forall L (l : list (sptr * Z)) x,
(exists b, In b l /\ loc_addr L (LMem (fst b)) <= x < loc_addr L (LMem (fst b)) + snd b) \/
(forall b, In b l -> ~ (loc_addr L (LMem (fst b)) <= x < loc_addr L (LMem (fst b)) + snd b)).
Proof.
intros L l x. induction l as [|b bs IH].
- right. intros b [].
- destruct (Z_le_dec (loc_addr L (LMem (fst b))) x) as [H1|H1];
[destruct (Z_lt_dec x (loc_addr L (LMem (fst b)) + snd b)) as [H2|H2]|].
+ left. exists b. split; [apply in_eq | lia].
+ destruct IH as [(b' & Hb' & Hx') | Hn]; [left; exists b'; split; [apply in_cons; exact Hb' | exact Hx'] |].
right. intros b' [<- | Hb']; [lia | apply Hn; exact Hb'].
+ destruct IH as [(b' & Hb' & Hx') | Hn]; [left; exists b'; split; [apply in_cons; exact Hb' | exact Hx'] |].
right. intros b' [<- | Hb']; [lia | apply Hn; exact Hb'].
Qed.
Theorem MRc_laws : MR_laws B (MRc B).
Proof.
split.
-   intros L A mem md M. exact (mc_wf _ _ _ _ _ M).
-   intros L A mem md p n i M Hin Hi. exact (blocks_facts L A mem md p n i M Hin Hi).
-   intros L A mem md p n M Hin.
destruct (block_region A p n (mc_wf _ _ _ _ _ M) Hin) as (k & o & rg & -> & Hrg & _ & Hlive & _ & _ & _ & Ho16).
unfold ptr_addr. cbn [loc_addr].
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k rg Hrg Hlive) as (Hal & _).
unfold PGSZ in Hal. apply Z.div_exact in Hal; [|lia]. apply Z.div_exact in Ho16; [|lia].
rewrite Hal, Ho16.
replace (4096 * (ly_reg L k / 4096) + 16 * (o / 16)) with ((256 * (ly_reg L k / 4096) + o / 16) * 16) by lia.
apply Z_mod_mult.
-   intros L A mem md p n M Hin.
destruct (block_region A p n (mc_wf _ _ _ _ _ M) Hin) as (k & o & rg & -> & Hrg & _ & Hlive & Ho & Hn & Hlen & _).
unfold ptr_addr. cbn [loc_addr].
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ M) k rg Hrg Hlive) as (_ & H1 & H2 & _). lia.
-   intros L A mem md M. unfold blocks.
rewrite <- (map_ext (block_range L) (fun b => (ptr_addr L (fst b), snd b))) by (intros [q k]; reflexivity).
apply user_blocks_disjoint; [exact (mc_wf _ _ _ _ _ M) | exact (mc_layout _ _ _ _ _ M)].
-   intros L A mem mem' md md' M Hown Hpres Hblk Hvm Hh Hlz Hmat.
pose proof (mc_wf _ _ _ _ _ M) as HW. pose proof (mc_layout _ _ _ _ _ M) as HL.
split; try (exact (mc_syms _ _ _ _ _ M) || exact HW || exact HL || exact (mc_bounded _ _ _ _ _ M) ||
exact (mc_ctx _ _ _ _ _ M) || exact (mc_sec _ _ _ _ _ M) || exact (mc_tail_geom _ _ _ _ _ M)).
+   apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) (mc_cells _ _ _ _ _ M) c Hc) as Hcell.
unfold cell_mem in *. destruct c as [l w v]; cbn [mc_loc mc_w mc_val] in *.
destruct v; try (intros k Hk; rewrite Hown; [apply Hcell; exact Hk | left; apply (image_cell_owned L A _ k HW HL Hc Hk)]).
intros Hw. destruct (Hcell Hw) as (b & Hb & Hz). exists b. split; [|exact Hz].
rewrite Hown; [| left].
* exact Hb.
* replace (loc_addr L l) with (loc_addr L l + Z.of_nat 0) by lia. apply (image_cell_owned L A _ 0%nat HW HL Hc Hw).
+   apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) (mc_tail _ _ _ _ _ M) c Hc) as Hcell.
pose proof (proj1 (Forall_forall _ _) (mc_tail_geom _ _ _ _ _ M) c Hc) as Hg. cbn beta in Hg.
unfold cell_mem in *. destruct c as [l w v]; cbn [mc_loc mc_w mc_val] in *.
destruct v; try (intros k Hk; rewrite Hown; [apply Hcell; exact Hk | left; apply Hg; exact Hk]).
intros Hw. destruct (Hcell Hw) as (b & Hb & Hz). exists b. split; [|exact Hz].
rewrite Hown; [exact Hb | left]. replace (loc_addr L l) with (loc_addr L l + Z.of_nat 0) by lia. apply Hg. exact Hw.
+   apply Forall_forall. intros rg Hrg.
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ M) rg Hrg) as Hf.
unfold foot_ok in *. destruct rg as [[o|q] len]; cbn [fst snd] in *; [exact I|].
intros x Hx.
destruct (in_block_dec L (user_blocks A) x) as [([p n] & Hb & Hbx) | Hnb0].
2: assert (Hnb : ~ in_user_block L A x) by (intros (b & Hb & Hbx); exact (Hnb0 b Hb Hbx)).
* cbn [fst snd] in Hbx. replace x with (ptr_addr L p + (x - ptr_addr L p)) by lia.
apply (Hblk p n); [exact Hb | unfold ptr_addr; lia].
* apply Hpres; [| apply Hf; exact Hx]. left. split; [| exact Hnb]. exists (LMem q, len). split; [exact Hrg | cbn [fst snd]; exact Hx].
+   pose proof (mc_statics _ _ _ _ _ M) as S.
assert (HS : forall a, static_owned B a -> mbyte segs mem' a = mbyte segs mem a) by (intros a Ha; apply Hown; right; exact Ha).
split.
* rewrite HS; [apply (st_needlocks _ _ S) | unfold static_owned; lia].
* intros k Hk. rewrite HS; [apply (st_pagesize _ _ S); exact Hk | unfold static_owned; lia].
* intros k Hk. rewrite HS; [apply (st_lock _ _ S); exact Hk | unfold static_owned; lia].
* intros k Hk. rewrite HS; [apply (st_got _ _ S); exact Hk | unfold static_owned; lia].
* destruct (st_guard _ _ S) as (g & Hg). exists g. intros k Hk. rewrite HS; [apply Hg; exact Hk | unfold static_owned; lia].
* intros a Ha. rewrite HS; [apply (st_tables _ _ S); exact Ha | unfold static_owned; unfold table_addr in Ha; lia].
+   pose proof (mc_ledger _ _ _ _ _ M) as G. destruct (mc_md _ _ _ _ _ M) as (_ & Hlz0 & Hmat0).
split; rewrite ?Hvm; try (apply G).
rewrite (vm_backing_used_ext md md' Hvm) by congruence. apply G.
+   auto.
-   intros L A mem md a M Ho. exact (owned_low L A mem md a M Ho).
-   intros L A mem md M. exact (mc_md _ _ _ _ _ M).
-   intros L A mem md M. exact (lg_ceil _ _ _ _ (mc_ledger _ _ _ _ _ M)).
Qed.
End h.
Section j.
Variable B : malloc_syms.
Let segs := ms_segs B.
Definition layout0 (brk0 sec : Z) : layout := Layout (ms_ctx B) (fun _ => 0) brk0 sec.
Lemma image_init_cells :
Forall (fun c => match c with
| MCell (LCtx off) w (VZ 0) => 0 <= off /\ off + Z.of_nat w <= CTX_SIZE
| _ => False end) (image init_state).
Proof.
rewrite image_init. apply Forall_forall. intros c Hc.
assert (H : forallb (fun c => match c with
| MCell (LCtx off) w (VZ z) => (0 <=? off) && (off + Z.of_nat w <=? CTX_SIZE) && (z =? 0)
| _ => false end) (ctx_cells init_state) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H c Hc).
destruct c as [[off|q] w [z|p|z|]]; try discriminate.
apply andb_prop in H as [H Hz]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in Hz. subst z. apply Z.leb_le in H1. apply Z.leb_le in H2. auto.
Qed.
Lemma alloc_ceiling_lt : alloc_ceiling < 2 ^ 63.
Proof. pose proof alloc_ceiling_val. lia. Qed.
Lemma le_byte_0 : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Theorem MRc_init : forall mem md sec,
syms_ok B -> heap_pristine B mem md -> 0 <= sec < 2 ^ 64 ->
MRc B (layout0 (bv_unsigned (vm_brk (m_vmmaps md))) sec) init_state mem md.
Proof.
intros mem md sec SO HP Hsec.
destruct (hp_vm _ _ _ HP) as (Hmaps & Hna & Hbrk & Hvalid & Hceil & Hres & Hlim & Hback).
destruct Hvalid as (Hrt & _ & Hal).
split.
- exact SO.
- apply wf_init.
- apply (proj2 init_ok).
-   split; [| split; [| split]].
+ cbn. exact (so_ctx_al _ SO).
+ intros k rg Hk. unfold region_of in Hk. cbn in Hk. destruct k; discriminate.
+ rewrite footprint_init. cbn. split; [intros y []| exact I].
+ rewrite footprint_init. intros rg [<-|[]]. unfold crange. cbn [fst snd loc_addr layout0 ly_ctx].
pose proof (so_ctx_lo _ SO). pose proof (so_ctx_hi _ SO). pose proof alloc_ceiling_lt. lia.
- reflexivity.
-   exact Hsec.
-   apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) image_init_cells c Hc) as H. cbn beta in H.
destruct c as [[off|q] w [z|p|z|]]; try contradiction. destruct z; try contradiction.
destruct H as [H1 H2]. unfold cell_mem. cbn [mc_loc mc_val mc_w loc_addr layout0 ly_ctx sval_num].
intros k Hk. rewrite le_byte_0. rewrite <- Z.add_assoc. apply (hp_ctx _ _ _ HP). lia.
-   change (tail_cells init_state) with (@nil mcell). constructor.
-   unfold tail_geom. change (tail_cells init_state) with (@nil mcell). constructor.
-   rewrite footprint_init. constructor; [exact I | constructor].
-   split.
+ apply (hp_needlocks _ _ _ HP).
+ apply (hp_pagesize _ _ _ HP).
+ apply (hp_lock _ _ _ HP).
+ apply (hp_got _ _ _ HP).
+ apply (hp_guard _ _ _ HP).
+ intros a Ha. apply (hp_tables _ _ _ HP). unfold table_addr in Ha. exact Ha.
-   split; cbn [layout0 ly_brk0 ly_reg st_brk init_state].
+ exact Hres.
+ exact Hlim.
+ intros r rg Hr. unfold region_of in Hr. cbn in Hr. destruct r; discriminate.
+ intros r rg off Hr. unfold region_of in Hr. cbn in Hr. destruct r; discriminate.
+ pose proof (so_rtop _ SO). unfold PGSZ, page_size in *. rewrite Hbrk in *. repeat split; lia.
+ reflexivity.
+ intros r rg Hr. unfold region_of in Hr. cbn in Hr. destruct r; discriminate.
+ rewrite Hmaps. cbn. lia.
+ rewrite Hmaps. constructor.
+ cbn. lia.
+   exact (hp_ceil _ _ _ HP).
- exact (hp_model _ _ _ HP).
Qed.
Corollary MRc_init_ex : forall mem md sec,
syms_ok B -> heap_pristine B mem md -> 0 <= sec < 2 ^ 64 ->
exists L, MRc B L init_state mem md /\ ly_sec L = sec.
Proof. intros mem md sec SO HP Hsec. exists (layout0 (bv_unsigned (vm_brk (m_vmmaps md))) sec). split; [apply MRc_init; assumption | reflexivity]. Qed.
End j.
Section m.
Variable B : malloc_syms.
Definition memrep (L : layout) (A : astate) (mem : word -> option byte) : Prop :=
Forall (cell_mem B L mem) (image A) /\
Forall (cell_mem B L mem) (tail_cells A) /\
Forall (foot_ok L mem) (footprint A).
Lemma MRc_memrep : forall L A mem md, MRc B L A mem md -> memrep L A mem.
Proof. intros L A mem md M. split; [| split]; [exact (mc_cells _ _ _ _ _ M) | exact (mc_tail _ _ _ _ _ M) | exact (mc_foot _ _ _ _ _ M)]. Qed.
Lemma MRc_intro : forall L A mem md,
syms_ok B -> WF A -> bounded A -> layout_ok L A -> ly_ctx L = ms_ctx B -> 0 <= ly_sec L < 2 ^ 64 ->
memrep L A mem -> tail_geom L A -> statics_ok B mem -> ledger_ok B L A md ->
m_halted md = None -> m_vm_lazy md = [] -> m_vm_materialized md = [] ->
MRc B L A mem md.
Proof. intros L A mem md SO HW HB HL Hc Hs (M1 & M2 & M3) TG ST LG H1 H2 H3. split; auto. Qed.
Lemma memrep_cell : forall L A mem c,
memrep L A mem -> In c (image A) -> cell_mem B L mem c.
Proof. intros L A mem c (M & _ & _) Hin. exact (proj1 (Forall_forall _ _) M c Hin). Qed.
Lemma memrep_tail : forall L A mem c,
memrep L A mem -> In c (tail_cells A) -> cell_mem B L mem c.
Proof. intros L A mem c (_ & M & _) Hin. exact (proj1 (Forall_forall _ _) M c Hin). Qed.
Lemma memrep_present : forall L A mem k rg x,
memrep L A mem -> region_of A k = Some rg -> rg_kind rg = RkMap -> rg_live rg = true ->
ly_reg L k <= x < ly_reg L k + rg_len rg -> present mem x.
Proof.
intros L A mem k rg x (_ & _ & M) Hr Hk Hl Hx.
pose proof (proj1 (Forall_forall _ _) M _ (footprint_region_In A k rg Hr Hk Hl)) as Hf.
cbn [foot_ok fst snd loc_addr] in Hf. apply Hf. lia.
Qed.
End m.
Section t.
Variable B : malloc_syms.
Let segs := ms_segs B.
Fixpoint rw_check (a : Z) (n : nat) : bool :=
match n with
| O => true
| S n' =>
match find_segment segs a 1 with
| Some seg =>
seg_writable seg &&
match segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) with Some _ => true | None => false end &&
match seg_rom segs (w64 a) with Some _ => true | None => false end &&
rw_check (a + 1) n'
| None => false
end
end.
Lemma rw_check_sound : forall n a,
rw_check a n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
forall mem x, a <= x < a + Z.of_nat n -> writable_at segs mem x /\ exists b, mbyte segs mem x = Some b.
Proof.
induction n as [|n IH]; intros a H Ha Hn mem x Hx; [lia|].
cbn [rw_check] in H.
destruct (find_segment segs a 1) as [seg|] eqn:Hseg; [|discriminate].
apply andb_prop in H as [H Hrec]. apply andb_prop in H as [H Hrom]. apply andb_prop in H as [Hw Hb].
destruct (Z.eq_dec x a) as [->|Hne].
- split.
+ unfold writable_at, wview. destruct (mem (Z_to_bv 64 a)); [discriminate|].
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite Hseg, Hw. destruct (segment_byte_at _ _); [discriminate | discriminate].
+ unfold mbyte. destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
unfold w64 in Hrom. destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | discriminate].
- apply (IH (a + 1)); [exact Hrec | lia | lia | lia].
Qed.
Definition covered (lo len : Z) : bool :=
existsb (fun s : word * word => (bv_unsigned (fst s) <=? lo) && (lo + len <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
(segments_reserved segs).
Lemma covered_sound : forall lo len a, covered lo len = true -> lo <= a < lo + len -> in_img B a.
Proof.
intros lo len a H Ha. unfold covered in H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
split.
- unfold segs in Hs. intros E. unfold segments_reserved in Hs. rewrite E in Hs. destruct Hs.
- exists s. split; [exact Hs | lia].
Qed.
Definition static_ranges : list (Z * Z) :=
[(ms_lock B, 4); (ms_libc B + 3, 1); (ms_libc B + 8, 8); (ms_libc B + 48, 8); (ms_got_guard B, 8); (ms_guard B, 8);
(ms_debruijn B - 108, 140); (ms_size_classes B, 96); (ms_small_cnt B, 27); (ms_med_cnt B, 4)].
Lemma static_owned_ranges : forall a, static_owned B a -> exists r, In r static_ranges /\ fst r <= a < fst r + snd r.
Proof.
intros a H. unfold static_owned in H. unfold static_ranges.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]];
[ exists (ms_lock B, 4) | exists (ms_libc B + 3, 1) | exists (ms_libc B + 8, 8) | exists (ms_libc B + 48, 8)
| exists (ms_got_guard B, 8) | exists (ms_guard B, 8) | exists (ms_debruijn B - 108, 140) | exists (ms_size_classes B, 96)
| exists (ms_small_cnt B, 27) | exists (ms_med_cnt B, 4) ];
(split; [cbn; tauto | cbn [fst snd]; lia]).
Qed.
Definition byte_img (a : Z) : Z := match seg_rom segs (w64 a) with Some b => bv_unsigned b | None => -1 end.
Definition syms_check : bool :=
(ms_ctx B mod 8 =? 0) && (4096 <=? ms_ctx B) && (ms_ctx B + CTX_SIZE <=? CEIL_MIN) &&
(4096 <=? reserved_top (segments_reserved segs)) &&
rw_check (ms_ctx B) (Z.to_nat CTX_SIZE) && (ms_ctx B + CTX_SIZE <=? 2 ^ 63) &&
covered (ms_ctx B) CTX_SIZE &&
forallb (fun r => covered (fst r) (snd r)) static_ranges &&
forallb (fun s : word * word => (0 <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) + bv_unsigned (snd s) <=? CEIL_MIN))
(segments_reserved segs) &&
forallb (fun k => byte_img (ms_size_classes B + 2 * Z.of_nat k) + 256 * byte_img (ms_size_classes B + 2 * Z.of_nat k + 1)
=? nth k size_classes 0) (seq 0 48) &&
forallb (fun k => (0 <=? byte_img (ms_size_classes B + 2 * Z.of_nat k)) && (0 <=? byte_img (ms_size_classes B + 2 * Z.of_nat k + 1))) (seq 0 48) &&
forallb (fun rc => byte_img (ms_small_cnt B + Z.of_nat rc) =? nth (rc mod 3) (nth (rc / 3) small_cnt_tab []) 0) (seq 0 27) &&
forallb (fun c => byte_img (ms_med_cnt B + Z.of_nat c) =? nth c med_cnt_tab 0) (seq 0 4) &&
forallb (fun k => byte_img (ms_debruijn B + Z.shiftr ((2 ^ Z.of_nat k * 125613361) mod 2 ^ 32) 27) =? Z.of_nat k) (seq 0 32).
Lemma byte_img_some : forall a v, byte_img a = v -> 0 <= v -> exists b, seg_rom segs (w64 a) = Some b /\ bv_unsigned b = v.
Proof.
intros a v H Hv. unfold byte_img in H. destruct (seg_rom segs (w64 a)) as [b|]; [exists b; auto | lia].
Qed.
Lemma syms_ok_of_check : syms_check = true -> syms_ok B.
Proof.
intros H. unfold syms_check in H.
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [H ?] end.
apply Z.eqb_eq in H.
repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X end.
rename H0 into Hdb. rename H1 into Hmed. rename H2 into Hsmall. rename H3 into Hsc0. rename H4 into Hsc.
rename H5 into Hsegs. rename H6 into Hcovst. rename H7 into Hcovctx. rename H8 into H63. rename H9 into Hrw.
rename H10 into Hrt. rename H11 into Hhi. rename H12 into Hlo.
pose proof alloc_ceiling_val as Hacv.
split; try assumption; try (clear -Hhi Hacv; lia).
- intros mem a Ha. apply (rw_check_sound (Z.to_nat CTX_SIZE) (ms_ctx B) Hrw); unfold CTX_SIZE in *; lia.
- intros a Ha. eapply covered_sound; [exact Hcovctx | exact Ha].
- intros a Ha. destruct (static_owned_ranges a Ha) as (r & Hr & Har).
rewrite forallb_forall in Hcovst. eapply covered_sound; [apply Hcovst; exact Hr | exact Har].
- intros a [_ (s & Hs & Ha)]. rewrite forallb_forall in Hsegs. specialize (Hsegs s Hs).
apply andb_prop in Hsegs as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. clear -X1 X2 Ha Hacv. lia.
- intros k Hk. rewrite forallb_forall in Hsc. rewrite forallb_forall in Hsc0.
assert (Hin : In k (seq 0 48)) by (apply in_seq; lia).
specialize (Hsc k Hin). specialize (Hsc0 k Hin). apply Z.eqb_eq in Hsc. apply andb_prop in Hsc0 as [X1 X2].
apply Z.leb_le in X1. apply Z.leb_le in X2.
destruct (byte_img_some _ _ eq_refl X1) as (lo & Hlo1 & Hlo2). destruct (byte_img_some _ _ eq_refl X2) as (hi & Hhi1 & Hhi2).
exists lo, hi. split; [exact Hlo1|]. split; [exact Hhi1|]. rewrite Hlo2, Hhi2. exact Hsc.
- intros r c Hr Hc. rewrite forallb_forall in Hsmall.
assert (Hin : In (3 * r + c)%nat (seq 0 27)) by (apply in_seq; lia).
specialize (Hsmall _ Hin). apply Z.eqb_eq in Hsmall.
replace ((3 * r + c) mod 3)%nat with c in Hsmall.
2:{ apply (Nat.mod_unique (3 * r + c) 3 r c); lia. }
replace ((3 * r + c) / 3)%nat with r in Hsmall.
2:{ apply (Nat.div_unique (3 * r + c) 3 r c); lia. }
assert (Hnn : 0 <= nth c (nth r small_cnt_tab []) 0).
{ do 9 (destruct r as [|r]; [cbn; do 3 (destruct c as [|c]; [cbn; lia|]); destruct c; cbn; lia|]). cbn. destruct c; cbn; [lia|]. destruct c; lia. }
exact (byte_img_some _ _ Hsmall Hnn).
- intros c Hc. rewrite forallb_forall in Hmed.
assert (Hin : In c (seq 0 4)) by (apply in_seq; lia). specialize (Hmed _ Hin). apply Z.eqb_eq in Hmed.
apply (byte_img_some _ _ Hmed). do 4 (destruct c as [|c]; [cbn; lia|]). cbn. destruct c; lia.
- intros k Hk. rewrite forallb_forall in Hdb.
assert (Hin : In (Z.to_nat k) (seq 0 32)) by (apply in_seq; lia). specialize (Hdb _ Hin). apply Z.eqb_eq in Hdb.
rewrite Z2Nat.id in Hdb by lia. apply (byte_img_some _ _ Hdb). lia.
Qed.
End t.
End e.
