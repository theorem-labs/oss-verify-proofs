(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN17.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN13.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in *.
Local Open Scope mm_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition aidx_of (sc cnt : Z) : Z :=
let a0 := (4096 - UNIT) / class_size sc - 1 in
let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in
if a1 <? 0 then 0 else a1.
Definition am_inst0 (sc cnt maplen aidx : Z) (r : nat) : ameta :=
mkAMeta None None (SP r 0) (ones aidx - 1) (ones (cnt - 1) - ones aidx) (cnt - 1) sc maplen aidx (repeat slot_zero (Z.to_nat cnt)).
Definition am_inst (m : sptr) (sc cnt maplen aidx : Z) (r : nat) : ameta :=
am_set_links (Some m) (Some m) (am_inst0 sc cnt maplen aidx r).
Definition inst_st (sc : Z) (m : sptr) (cnt needed : Z) (s : astate) : astate :=
let r := length (st_regions s) in
let aidx := aidx_of sc cnt in
let s1 := set_regions (st_regions s ++ [YO0i.mkRegion RkMap needed [] true]) s in
let s2 := set_mmap_counter (Z.land (st_mmap_counter s + 1) (2 ^ 32 - 1)) s1 in
let s3 := set_usage (zset sc (usage_of s sc + cnt) (st_usage s)) s2 in
let s4 := upd_meta m (MUsed (am_inst0 sc cnt (needed / 4096) aidx r)) s3 in
let s5 := upd_meta m (MUsed (am_inst m sc cnt (needed / 4096) aidx r)) s4 in
set_active (lupd (st_active s) (Z.to_nat sc) (Some m)) s5.
Lemma mm_granted_eq : forall sc m cnt needed s,
active_hd s sc = None -> needed mod 4096 = 0 ->
mm_granted sc m cnt needed s = IRet (Some m, inst_st sc m cnt needed s).
Proof.
intros sc m cnt needed s Hhd Hmod. unfold active_hd in Hhd.
unfold mm_granted, new_region, install_group, set_usage_of, setm, queue, get_links, massert, get_head, set_links, set_head, setslot, modify, bind, get, put, ret.
rewrite (page_round_fixed needed) by (unfold PGSZ; exact Hmod).
cbn - [ones class_size Z.sub Z.add Z.div Z.mul Z.ltb Z.land Z.pow zset usage_of Z.to_nat repeat aidx_of UNIT].
rewrite mlookup_mupdate_same.
cbn - [ones class_size Z.sub Z.add Z.div Z.mul Z.ltb Z.land Z.pow zset usage_of Z.to_nat repeat aidx_of UNIT].
rewrite Hhd.
cbn - [ones class_size Z.sub Z.add Z.div Z.mul Z.ltb Z.land Z.pow zset usage_of Z.to_nat repeat aidx_of UNIT].
rewrite mlookup_mupdate_same.
cbn - [ones class_size Z.sub Z.add Z.div Z.mul Z.ltb Z.land Z.pow zset usage_of Z.to_nat repeat aidx_of UNIT].
reflexivity.
Qed.
Lemma mupdate_mupdate : forall l p x y, mupdate (mupdate l p x) p y = mupdate l p y.
Proof.
induction l as [|[q z] t IH]; intros p x y; cbn; [rewrite sptr_eqb_refl; reflexivity|].
destruct (sptr_eqb p q) eqn:E; cbn; rewrite E; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Section c.
Variables (sc : Z) (m : sptr) (cnt needed : Z) (s : astate).
Let r : nat := length (st_regions s).
Let am1 : ameta := am_inst m sc cnt (needed / 4096) (aidx_of sc cnt) r.
Let s5 : astate := inst_st sc m cnt needed s.
Lemma inst_fields :
st_metas s5 = mupdate (st_metas s) m (MUsed am1) /\
st_regions s5 = st_regions s ++ [YO0i.mkRegion RkMap needed [] true] /\
st_areas s5 = st_areas s /\ st_brk s5 = st_brk s /\
st_active s5 = lupd (st_active s) (Z.to_nat sc) (Some m) /\
st_usage s5 = zset sc (usage_of s sc + cnt) (st_usage s) /\
st_mmap_counter s5 = Z.land (st_mmap_counter s + 1) (2 ^ 32 - 1) /\
st_init_done s5 = st_init_done s /\ st_free_meta_head s5 = st_free_meta_head s /\ st_avail_meta s5 = st_avail_meta s /\
st_avail_meta_count s5 = st_avail_meta_count s /\ st_avail_meta_area_count s5 = st_avail_meta_area_count s /\
st_meta_alloc_shift s5 = st_meta_alloc_shift s /\ st_area_head s5 = st_area_head s /\ st_area_tail s5 = st_area_tail s /\
st_avail_meta_areas s5 = st_avail_meta_areas s /\ st_unmap_seq s5 = st_unmap_seq s /\ st_bounces s5 = st_bounces s /\ st_seq s5 = st_seq s.
Proof.
subst s5 am1 r. unfold inst_st, upd_meta. cbn. rewrite mupdate_mupdate. repeat split; reflexivity.
Qed.
Lemma inst_MT : forall q, MT s5 q = if sptr_eqb q m then Some (MUsed am1) else MT s q.
Proof. intros q. unfold MT. rewrite (proj1 inst_fields). destruct (sptr_eqb q m) eqn:E; [apply sptr_eqb_eq in E; subst; apply mlookup_mupdate_same | apply sptr_eqb_neq in E; apply mlookup_mupdate_other; exact E]. Qed.
Lemma inst_keys : In m (keys s) -> keys s5 = keys s.
Proof. intros Hm. unfold keys. rewrite (proj1 inst_fields). fold (keys s). exact (keys_upd_In m (MUsed am1) s Hm). Qed.
Lemma inst_region_of : forall k, region_of s5 k = if Nat.ltb k r then region_of s k else if Nat.eqb k r then Some (YO0i.mkRegion RkMap needed [] true) else None.
Proof. intros k. exact (region_of_new s s5 _ k (proj1 (proj2 inst_fields))). Qed.
End c.
Lemma used_metas_ins : forall s q am x, MT s q = Some x -> nonusedb (Some x) = true ->
exists u1 u2, used_metas s = u1 ++ u2 /\ used_metas (upd_meta q (MUsed am) s) = u1 ++ (q, am) :: u2.
Proof.
intros s q am x. unfold MT, used_metas, upd_meta. cbn. induction (st_metas s) as [|[p y] t IH]; cbn; intros H Hx; [discriminate|].
destruct (sptr_eqb q p) eqn:E.
- apply sptr_eqb_eq in E. subst p. injection H as ->. cbn.
exists [], (flat_map (fun e : sptr * mslot => let (p0, m0) := e in match m0 with MUsed am0 => [(p0, am0)] | _ => [] end) t).
destruct x as [| |a]; cbn in Hx; try discriminate; (split; [reflexivity | reflexivity]).
- destruct (IH H Hx) as (u1 & u2 & E1 & E2). cbn. rewrite E1, E2.
exists (match y with MUsed a0 => [(p, a0)] | _ => [] end ++ u1), u2. split; [rewrite app_assoc; reflexivity|]. rewrite app_assoc. reflexivity.
Qed.
Lemma areas_cells_MT_ext : forall s s' l, (forall q, MT s' q = MT s q) -> areas_cells s' l = areas_cells s l.
Proof.
intros s s' l H. induction l as [|a t IH]; [reflexivity|]. cbn [areas_cells]. rewrite IH. f_equal. unfold area_cells. f_equal.
apply YN2c.flat_map_ext_in. intros k _. exact (f_equal (meta_slot_cells _) (H (padd a (AREA_HDR + META_SIZE * Z.of_nat k)))).
Qed.
Section d.
Variables (L : layout) (A : astate) (md : Model).
Hypothesis LG : ledger_ok B L A md.
Hypothesis LX : ledger_x L A md.
Hypothesis NN : forall k rg, region_of A k = Some rg -> 0 <= rg_len rg.
Hypothesis MD : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Let N := length (st_regions A).
Lemma ledger_new_map : forall A' (a : word) (n : Z),
0 < n -> n mod PGSZ = 0 -> grant_ok (Z_to_bv 64 0) md a n = true ->
st_regions A' = st_regions A ++ [YO0i.mkRegion RkMap n [] true] -> st_brk A' = st_brk A ->
(forall r p, st_brk A = BrkCur r p -> (r < N)%nat) ->
ledger_ok B (Lset L A (bv_unsigned a)) A' (mmap_model a (Z_to_bv 64 n) md) /\
ledger_x (Lset L A (bv_unsigned a)) A' (mmap_model a (Z_to_bv 64 n) md).
Proof.
intros A' a n Hn Hpg GR ER EB BR.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
destruct (grant_ok_unpack _ _ _ _ GR) as (Hal & Hpos & Htop & RF & Hbk). unfold page_size in Hal.
assert (Hceil : bv_unsigned a + n <= alloc_ceiling).
{ apply (YM05.grant_below_ceil _ _ (lg_ceil _ _ _ _ LG)); [| exact Htop].
rewrite Z.add_mod, Hal by lia. unfold PGSZ in Hpg. rewrite Hpg. reflexivity. }
assert (NU : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_w64; lia).
assert (VM : vm_maps (m_vmmaps (mmap_model a (Z_to_bv 64 n) md)) = (a, Z_to_bv 64 n) :: vm_maps (m_vmmaps md)) by reflexivity.
assert (VN : vm_noaccess (m_vmmaps (mmap_model a (Z_to_bv 64 n) md)) = vm_noaccess (m_vmmaps md)) by reflexivity.
assert (VR : vm_reserved (m_vmmaps (mmap_model a (Z_to_bv 64 n) md)) = vm_reserved (m_vmmaps md)) by reflexivity.
assert (VL : vm_limit (m_vmmaps (mmap_model a (Z_to_bv 64 n) md)) = vm_limit (m_vmmaps md)) by reflexivity.
assert (VS : vm_start_brk (m_vmmaps (mmap_model a (Z_to_bv 64 n) md)) = vm_start_brk (m_vmmaps md)) by reflexivity.
assert (VB' : vm_brk (m_vmmaps (mmap_model a (Z_to_bv 64 n) md)) = vm_brk (m_vmmaps md)) by reflexivity.
pose proof (fun k => region_of_new A A' _ k ER) as RO. cbn beta in RO. fold N in RO.
pose proof (live_bytes_new A A' _ ER eq_refl) as LB. cbn [rg_len] in LB.
pose proof (nslots_new A A' _ ER) as NS. unfold region_slots in NS. cbn [rg_live rg_kind] in NS.
pose proof (live_bytes_nonneg' A NN) as LNN.
pose proof (fresh_region L A md LX a n Hn Hpos ltac:(lia) RF) as FRG. pose proof (fresh_entry L A md LX a n Hn Hpos ltac:(lia) RF) as FE.
pose proof (fresh_img B L A md LG a n Hn Hpos ltac:(lia) RF) as FI.
split.
- split; rewrite ?VM, ?VN, ?VR, ?VL, ?VS, ?VB'.
+ exact (lg_reserved _ _ _ _ LG).
+ exact (lg_limit _ _ _ _ LG).
+ intros k rg Hk Hl Hkind. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* right. rewrite (Lset_lt L A _ k H). exact (lg_maps _ _ _ _ LG k rg Hk Hl Hkind).
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. left. unfold w64. rewrite Lset_new, w64_u64. reflexivity.
+ intros k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* unfold w64 in *. rewrite (Lset_lt L A _ k H). destruct (lg_noaccess _ _ _ _ LG k rg off Hk Hl Hkind Ho1 Ho2 Ho3 Hrw) as [N1 N2].
split; [exact N1 | apply map_contains_cons'; exact N2].
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. discriminate.
+ exact (lg_brk0 _ _ _ _ LG).
+ rewrite EB. pose proof (lg_brk _ _ _ _ LG) as HB. destruct (st_brk A) as [| |r p] eqn:Ebk; try exact HB.
rewrite (Lset_lt L A _ r (BR r p eq_refl)). exact HB.
+ intros k rg Hk Hl. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* rewrite (Lset_lt L A _ k H). exact (lg_placed _ _ _ _ LG k rg Hk Hl).
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. rewrite Lset_new. cbn [rg_len].
split; [exact Hal|]. split; [apply Z.mod_divide in Hal; [destruct Hal as [q Hq]; lia | lia]|].
split; [exact Hceil|]. intros x Hx Himg. exact (FI x Himg Hx).
+ cbn [length]. rewrite NS. pose proof (lg_count _ _ _ _ LG). lia.
+ rewrite LB. constructor.
* cbn [snd]. rewrite NU. lia.
* apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (lg_sizes _ _ _ _ LG) e He). cbn beta in *. lia.
+ rewrite LB. destruct MD as (_ & ML & MM).
pose proof (vm_backing_used_le_maps (mmap_model a (Z_to_bv 64 n) md) ltac:(rewrite mmap_model_lazy; exact ML) MM) as VB.
rewrite VM in VB. cbn [State.live_bytes] in VB. rewrite NU in VB. pose proof (lx_lb _ _ _ LX). lia.
+   exact (lg_ceil _ _ _ _ LG).
- split; rewrite ?VM.
+ intros k rg x Hk Hl Hx. rewrite RO in Hk. destruct (Nat.ltb_spec k N).
* rewrite (Lset_lt L A _ k H) in Hx. destruct (lx_cov _ _ _ LX k rg x Hk Hl Hx) as (e & He & Hex). exists e. split; [right; exact He | exact Hex].
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. rewrite Lset_new in Hx. cbn [reg_lo rg_kind rg_len] in Hx.
exists (a, Z_to_bv 64 n). split; [left; reflexivity|]. unfold iv_lo, iv_len. cbn [fst snd]. rewrite NU. lia.
+ intros e [<- | He]; [| exact (lx_maps _ _ _ LX e He)]. unfold iv_lo, iv_len; cbn [fst snd]. rewrite NU. lia.
+ intros e1 e2 [<- | H1] [<- | H2].
* left. reflexivity.
* right. pose proof (FE e2 H2) as D. unfold iv_lo, iv_len in *; cbn [fst snd]. rewrite NU. exact D.
* right. pose proof (FE e1 H1) as D. unfold ranges_disjoint, iv_lo, iv_len in *; cbn [fst snd] in *. rewrite NU. lia.
* exact (lx_disj _ _ _ LX e1 e2 H1 H2).
+ intros k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2. rewrite RO in H1, H2.
destruct (Nat.ltb_spec k1 N); destruct (Nat.ltb_spec k2 N).
* rewrite (Lset_lt L A _ k1 H), (Lset_lt L A _ k2 H0). exact (lx_regs _ _ _ LX k1 k2 rg1 rg2 Hne H1 H2 Hl1 Hl2 N1 N2).
* destruct (Nat.eqb_spec k2 N); [|discriminate]. injection H2 as <-. subst k2. rewrite (Lset_lt L A _ k1 H), Lset_new.
cbn [reg_lo rg_kind rg_len] in *. unfold ranges_disjoint; cbn [fst snd].
pose proof (FRG k1 rg1 (ly_reg L k1 + reg_lo rg1) H1 Hl1 ltac:(lia)).
pose proof (FRG k1 rg1 (bv_unsigned a) H1 Hl1). lia.
* destruct (Nat.eqb_spec k1 N); [|discriminate]. injection H1 as <-. subst k1. rewrite (Lset_lt L A _ k2 H0), Lset_new.
cbn [reg_lo rg_kind rg_len] in *. unfold ranges_disjoint; cbn [fst snd].
pose proof (FRG k2 rg2 (ly_reg L k2 + reg_lo rg2) H2 Hl2 ltac:(lia)).
pose proof (FRG k2 rg2 (bv_unsigned a) H2 Hl2). lia.
* destruct (Nat.eqb_spec k1 N); [|discriminate]. destruct (Nat.eqb_spec k2 N); [|discriminate]. exfalso. apply Hne. lia.
+ intros e [<- | He].
* exists N, (YO0i.mkRegion RkMap n [] true). rewrite RO, Nat.ltb_irrefl, Nat.eqb_refl. split; [reflexivity|]. split; [reflexivity|].
rewrite Lset_new. unfold iv_lo, iv_len; cbn [fst snd rg_len]. rewrite NU. lia.
* destruct (lx_in _ _ _ LX e He) as (k & rg & Hk & Hl & G1 & G2). exists k, rg.
pose proof (region_of_lt _ _ _ Hk) as HkN. fold N in HkN.
rewrite RO. rewrite (proj2 (Nat.ltb_lt k N) HkN). rewrite (Lset_lt L A _ k HkN). auto.
+ rewrite LB. cbn [State.live_bytes]. rewrite NU. pose proof (lx_lb _ _ _ LX). lia.
+
change (vm_noaccess (m_vmmaps (mmap_model a (Z_to_bv 64 n) md))) with (vm_noaccess (m_vmmaps md)).
intros e He. destruct (lx_noacc _ _ _ LX e He) as (E & HE & G1 & G2 & HR). exists E. split; [right; exact HE|].
split; [exact G1|]. split; [exact G2|]. intros k rg Hk Hl Hkd Hp0. rewrite RO in Hk.
destruct (Nat.ltb_spec k N).
* rewrite (Lset_lt L A _ k H). exact (HR k rg Hk Hl Hkd Hp0).
* destruct (Nat.eqb_spec k N); [|discriminate]. injection Hk as <-. subst k. rewrite Lset_new. cbn [rg_len].
pose proof (FE E HE) as D. unfold ranges_disjoint in *; cbn [fst snd] in *. lia.
Qed.
End d.
Lemma class_sum_le_X : forall X R U s sc, Inv X R U s -> 0 <= class_sum X s sc <= 32 * Z.of_nat (length (keys s)).
Proof.
intros X R U s sc HI. unfold class_sum.
assert (G : forall l, (forall g, In g l -> 0 <= contrib X s sc g <= 32) -> 0 <= fold_right (fun g acc => contrib X s sc g + acc) 0 l <= 32 * Z.of_nat (length l)).
{ induction l as [|x t IH]; intros H; cbn [fold_right length]; [lia|].
pose proof (H x (or_introl eq_refl)). assert (IH' := IH (fun g Hg => H g (or_intror Hg))). lia. }
apply G. intros g _. unfold contrib. destruct (MTX X s g) as [[| |am]|] eqn:E; try lia.
pose proof (inv_groups HI g am E) as ((M1 & _) & _). destruct (am_sc am =? sc); lia.
Qed.
Lemma usage_small : forall X R U s sc, Inv X R U s -> bounded s -> (forall k, U k = 0) -> 0 <= sc < 48 -> usage_of s sc + 32 < 2 ^ 48.
Proof.
intros X R U s sc HI HB HU Hsc. pose proof (inv_usage HI sc Hsc) as E. rewrite HU in E.
pose proof (class_sum_le_X X R U s sc HI) as CS. pose proof (keys_le_areas s (inv_keys HI)) as KA. destruct HB as (_ & _ & HA).
unfold METAS_PER_AREA in KA. change (2 ^ 36) with 68719476736 in HA. change (2 ^ 48) with 281474976710656. lia.
Qed.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
