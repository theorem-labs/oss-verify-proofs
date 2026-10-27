(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0a.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B1 := src0_msyms.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma present_writable segs mem a : present mem a -> writable_at segs mem a.
Proof. intros [b Hb]. unfold writable_at, wview. rewrite Hb. discriminate. Qed.
Lemma cell_bytes L mem loc w z :
cell_mem B1 L mem (MCell loc w (VZ z)) -> bytes_are mem (loc_addr L loc) w z.
Proof. intros H k Hk. exact (H k Hk). Qed.
Lemma cell_bytes_ptr L mem loc w q :
cell_mem B1 L mem (MCell loc w (VP q)) -> bytes_are mem (loc_addr L loc) w (ptr_addr L q).
Proof. intros H k Hk. exact (H k Hk). Qed.
Lemma cell_bytes_sec L mem loc w :
cell_mem B1 L mem (MCell loc w VSec) -> bytes_are mem (loc_addr L loc) w (ly_sec L).
Proof. intros H k Hk. specialize (H k Hk). cbn [mc_loc mc_w mc_val sval_num] in H. exact H. Qed.
Lemma bytes_are_eq m a a' w v v' : bytes_are m a w v -> a = a' -> v = v' -> bytes_are m a' w v'.
Proof. intros H <- <-. exact H. Qed.
Lemma in_img1_in_img a : in_img1 a -> in_img B1 a.
Proof.
intros H. unfold in_img1 in H.
set (nblk := Z.to_nat ((0x51000 - 0x10000) / 0x1000)) in *.
assert (C : forallb (fun k => existsb (fun s : word * word =>
(bv_unsigned (fst s) <=? 0x10000 + 0x1000 * Z.of_nat k) &&
(0x10000 + 0x1000 * Z.of_nat k + 0x1000 <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
(segments_reserved (ms_segs B1))) (seq 0 nblk) = true).
{ subst nblk. vm_compute. reflexivity. }
rewrite forallb_forall in C.
set (k := Z.to_nat ((a - 0x10000) / 0x1000)).
assert (LT : a - 0x10000 < 0x1000 * Z.of_nat nblk).
{ subst nblk. match goal with |- _ < ?r => let v := eval vm_compute in r in change r with v end. lia. }
assert (Hk : In k (seq 0 nblk)).
{ apply in_seq. split; [lia|]. cbn [Nat.add].
enough (Z.of_nat k < Z.of_nat nblk) by lia. subst k.
rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia. }
specialize (C k Hk). apply existsb_exists in C as (s & Hs & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
assert (Hk' : 0x10000 + 0x1000 * Z.of_nat k <= a < 0x10000 + 0x1000 * Z.of_nat k + 0x1000).
{ subst k. rewrite Z2Nat.id by (apply Z.div_pos; lia).
pose proof (Z.mul_div_le (a - 0x10000) 0x1000 ltac:(lia)). pose proof (Z.mul_succ_div_gt (a - 0x10000) 0x1000 ltac:(lia)). lia. }
split; [(first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. exists s. split; [exact Hs | lia].
Qed.
Lemma scl_range sc : 0 <= sc < 48 -> 1 <= znth sc size_classes <= 8191.
Proof.
intros H.
assert (T : forallb (fun k => (1 <=? znth k size_classes) && (znth k size_classes <=? 8191)) (zseq 0 48) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in T. specialize (T sc (proj2 (In_zseq 0 48 sc) ltac:(lia))).
apply andb_prop in T as [T1 T2]. apply Z.leb_le in T1. apply Z.leb_le in T2. lia.
Qed.
Lemma mask_u32 (m last : Z) : 0 <= m -> 0 <= last <= 31 -> (forall i, last < i -> Z.testbit m i = false) -> m < 2 ^ 32.
Proof.
intros Hm Hl Hb. apply (Z.lt_le_trans _ (2 ^ (last + 1))); [|apply Z.pow_le_mono_r; lia].
apply lt_pow2_of_testbit; [lia|lia|]. intros i Hi. apply Hb. lia.
Qed.
Definition scl_of (sc : Z) : Z := if sc <? 48 then znth sc size_classes else 1.
Definition kcase_of (am : ameta) : kcase :=
if am_sc am =? 63 then K3b
else if am_maplen am =? 0 then K1
else if am_last am =? 0 then K3a else K2.
Definition rcase_of (rsv : Z) : rcase :=
if rsv =? 0 then R0 else if rsv <? 5 then R14 else if rsv =? 5 then R5 else R6.
Definition fv_of (regs : bvmap 5 word) (L : layout) (g : sptr) (am : ameta) (idx : Z) (fr : frame) (a : sptr) (glen : Z) : fvals :=
FV regs (ptr_addr L g) (ptr_addr L (am_mem am)) (hdr_off16 am idx fr) (hdr_byte3 am idx fr) idx (reserved_of am fr) (meta_bits am)
(am_avail am) (am_freed am) (ptr_addr L a) (am_sc am) (scl_of (am_sc am)) (am_last am) (am_maplen am)
(ptr_addr L (slot_end am idx)) (ptr_addr L (frame_ptr am idx fr) + fr_n fr)
(ly_reg L (prid (am_mem am))) (ly_reg L (prid (am_mem am)) + glen)
(ly_sec L)  .
Lemma slot_arith stride idx last : 16 <= stride -> 0 <= idx <= last ->
0 <= stride * idx /\ stride * idx + stride <= stride * (last + 1).
Proof. intros. nia. Qed.
Section e.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis MR : MRc B1 L A mem md.
Hypothesis RSV : rsv_ok A.
Hypothesis Hu : usedX [] A g am.
Hypothesis Hidx : 0 <= idx <= am_last am.
Hypothesis Hfr : ss_fr (nth_slot am idx) = Some fr.
Hypothesis Hk : fr_kind fr = FUser.
Hypothesis Hin : In (frame_ptr am idx fr, fr_n fr) (user_blocks A).
Hypothesis Ha0 : getr regs 10 = Z_to_bv 64 (ptr_addr L (frame_ptr am idx fr)).
Hypothesis Hsp : spZ regs mod 16 = 0 /\ alloc_ceiling + ALLOC_STACK <= spZ regs /\ spZ regs < 2 ^ 63.
Hypothesis Hstk : forall x, spZ regs - ALLOC_STACK <= x < spZ regs -> writable_at src0segs mem x.
Hypothesis Harea : In a (st_areas A) /\ 0 <= ka < METAS_PER_AREA /\ g = padd a (AREA_HDR + META_SIZE * ka).
Hypothesis Hrg : region_of A (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg.
Let v := fv_of regs L g am idx fr a (rg_len rg).
Lemma WFA : WF A. Proof. exact (mc_wf _ _ _ _ _ MR). Qed.
Lemma LAY : layout_ok L A. Proof. exact (mc_layout _ _ _ _ _ MR). Qed.
Lemma free_pre_intro : free_pre (kcase_of am) (rcase_of (reserved_of am fr)) v mem.
Proof.
pose proof WFA as HW. pose proof LAY as HL. pose proof (mc_syms _ _ _ _ _ MR) as SO.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
pose proof (inv_groups HW g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & (Nf & Of & Bf & H16 & _) & Hhdr0).
pose proof (frames_intro A g am idx fr HW Mg Hidx Hfr) as Hframes.
pose proof (get_meta_ok A g am idx fr HW Hframes) as GM. cbn zeta in GM.
destruct GM as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & Hbase & _ & Hland & Hasserts & _).
destruct Harea as (Hain & Hka & Eg). destruct Hrg as (Hrg1 & Hrgk & Hrgl & Ho & Hext).
destruct Hsp as (Hsp16 & Hsplo & Hsphi).
pose proof (RSV g am idx fr Hframes Hk) as Hrsv.
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ MR) _ _ Hrg1 Hrgl) as (Ral & R4096 & Rceil & Rimg).
destruct (proj1 (proj2 (inv_areas HW)) a Hain) as (ra & oa & rga & Ea & Hoa & Hoa2 & Hra & Hral & Hoalen & Hrak).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ MR) _ _ Hra Hral) as (Aal & A4096 & Aceil & Aimg).
assert (Hbits : Z.testbit (am_freed am) idx = false /\ Z.testbit (am_avail am) idx = false).
{ unfold allocated in Hal. rewrite Z.lor_spec in Hal. destruct (Z.testbit (am_avail am) idx), (Z.testbit (am_freed am) idx); cbn in Hal; try discriminate; auto. }
destruct Hbits as [Hfb Hab].
assert (Hav32 : am_avail am < 2 ^ 32) by (apply (mask_u32 _ (am_last am)); [lia|lia|intros i Hi; apply (proj1 (Gabove i Hi))]).
assert (Hfr32 : am_freed am < 2 ^ 32) by (apply (mask_u32 _ (am_last am)); [lia|lia|intros i Hi; apply (proj2 (Gabove i Hi))]).
assert (Hsc : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _)|(C & _)]; [left|right]; exact C).
destruct (slot_arith (stride_of am) idx (am_last am) Sp Hidx) as [P1 P2].
pose proof alloc_ceiling_lt as HCE.
destruct (am_mem am) as [kr ko] eqn:Emem. cbn [prid poff] in *.
remember (ly_reg L kr) as GLO eqn:EGLO. remember (stride_of am) as ST eqn:EST.
assert (Est : ptr_addr L (slot_start am idx) = GLO + ko + 16 + ST * idx).
{ unfold ptr_addr, loc_addr, slot_start. rewrite Emem. cbn [padd]. subst ST GLO. unfold UNIT. lia. }
assert (Efp : ptr_addr L (frame_ptr am idx fr) = GLO + ko + 16 + ST * idx + 16 * fr_off fr).
{ unfold ptr_addr, loc_addr, frame_ptr, slot_start. rewrite Emem. cbn [padd]. subst ST GLO. unfold UNIT. lia. }
assert (Eend : ptr_addr L (slot_end am idx) = GLO + ko + 16 + ST * idx + ST - 4).
{ unfold ptr_addr, loc_addr, slot_end, slot_start. rewrite Emem. cbn [padd]. subst ST GLO. unfold UNIT, IB. lia. }
unfold group_extent, UNIT, IB in Hext. rewrite <- EST in Hext.
remember (ptr_addr L (frame_ptr am idx fr)) as P eqn:EPdef.
assert (EP : fv_p v = P).
{ unfold fv_p, v, fv_of. cbn [fv_regs]. rewrite Ha0. apply lit64_small. unfold UNIT, IB in Bf. lia. }
unfold UNIT, IB in Bf.
remember (ly_reg L ra) as ALO eqn:EALO.
assert (Ea' : ptr_addr L a = ALO + oa) by (unfold ptr_addr, loc_addr; rewrite Ea; subst ALO; reflexivity).
assert (Eg' : ptr_addr L g = ALO + oa + AREA_HDR + META_SIZE * ka).
{ unfold ptr_addr, loc_addr. rewrite Eg, Ea. cbn [padd]. subst ALO. lia. }
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
assert (Hrc : 0 <= rsv_code am fr <= 5 /\ (reserved_of am fr <= 5 -> rsv_code am fr = reserved_of am fr) /\ (5 <= reserved_of am fr -> rsv_code am fr = 5)).
{ unfold rsv_code, reserved_of, UNIT, IB in *. rewrite <- EST. destruct (5 <=? ST - 4 - 16 * fr_off fr - fr_n fr) eqn:E5;
[apply Z.leb_le in E5 | apply Z.leb_gt in E5]; repeat split; intros; lia. }
assert (Eh3 : hdr_byte3 am idx fr = idx + 32 * rsv_code am fr) by (unfold hdr_byte3; rewrite Hk; reflexivity).
assert (Hrsv' : reserved_of am fr = ST - 4 - 16 * fr_off fr - fr_n fr) by (unfold reserved_of, UNIT, IB; rewrite <- EST; reflexivity).
assert (Hoff16 : 0 <= hdr_off16 am idx fr) by (unfold hdr_off16, UNIT; rewrite <- EST; pose proof (Z.div_pos (ST * idx) 16); lia).
assert (Hpm : P = GLO + ko + 16 + 16 * hdr_off16 am idx fr).
{ pose proof (f_equal poff Hbase) as Hb. unfold frame_ptr, slot_start in Hb. rewrite Emem in Hb. cbn [padd poff] in Hb. unfold UNIT in Hb. lia. }
assert (Hdisj : GLO + rg_len rg <= ALO + oa \/ ALO + oa + 4096 <= GLO).
{ pose proof HL as (_ & _ & PW & _).
assert (In1 : In (LMem (SP kr 0), rg_len rg) (footprint A)) by (apply footprint_region_In; assumption).
assert (In2 : In (LMem a, PGSZ) (footprint A)) by (right; apply in_app_iff; left; apply in_map_iff; exists a; auto).
assert (Hne : (LMem (SP kr 0), rg_len rg) <> (LMem a, PGSZ)).
{ intros E. injection E as E1 E2. rewrite Ea in E1. injection E1 as <- Eo. rewrite Hrg1 in Hra. injection Hra as <-. rewrite Hrgk in Hrak. exact Hrak. }
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) _ _ PW In1 In2 Hne) as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; rewrite Ea in D; cbn [loc_addr] in D; subst GLO ALO; unfold PGSZ in D; lia. }
assert (Hscl : am_sc am < 48 -> 1 <= znth (am_sc am) size_classes <= 8191 /\ scl_of (am_sc am) = znth (am_sc am) size_classes).
{ intros Hlt. split; [apply scl_range; lia|]. unfold scl_of. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
unfold get_meta_asserts, view_of in Hasserts. cbn [gm_p4 gm_p3 gm_off16 gm_meta gm_mem gm_avail gm_freed gm_last gm_sc gm_maplen gm_area_check] in Hasserts.
rewrite Hland in Hasserts. apply andb_prop in Hasserts as [Hasserts Hml]. apply andb_prop in Hasserts as [_ Hcls].
assert (Hmlb : 0 < am_maplen am -> hdr_off16 am idx fr <= 256 * am_maplen am - 1).
{ intros Hm. unfold implb in Hml. replace (0 <? am_maplen am) with true in Hml by (symmetry; apply Z.ltb_lt; lia). cbn [negb orb] in Hml.
apply Z.leb_le in Hml. unfold UNIT in Hml.
replace (am_maplen am * 4096 / 16) with (256 * am_maplen am) in Hml; [lia|].
replace (am_maplen am * 4096) with (256 * am_maplen am * 16) by lia. rewrite Z_div_mult by lia. reflexivity. }
assert (Hclsb : am_sc am < 48 -> znth (am_sc am) size_classes * idx <= hdr_off16 am idx fr < znth (am_sc am) size_classes * (idx + 1)).
{ intros Hlt. replace (am_sc am <? 48) with true in Hcls by (symmetry; apply Z.ltb_lt; lia).
apply andb_prop in Hcls as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia. }
assert (Hml51 : am_maplen am < 2 ^ 51).
{ destruct (Z_lt_le_dec 0 (am_maplen am)) as [Hm|Hm]; [|lia].
destruct (Gmp Hm) as (r1 & rg1 & Em1 & Hr1 & _ & _ & Hlen1 & _). rewrite Emem in Em1. injection Em1 as <- Eko.
cbn [prid] in Hrg1. rewrite Hrg1 in Hr1. injection Hr1 as <-. unfold PGSZ in Hlen1. lia. }
pose proof (fun c (H : In c (image A)) => memrep_cell B1 L A mem c (MRc_memrep B1 L A mem md MR) H) as CELL.
pose proof (fun c (H : In c (tail_cells A)) => memrep_tail B1 L A mem c (MRc_memrep B1 L A mem md MR) H) as TAIL.
assert (Hum : In (g, am) (used_metas A)) by (apply (used_metas_iff A g am (proj1 (inv_keys HW))); exact Mg).
assert (Carea : In (MCell (LMem a) 8 VSec) (image A)).
{ unfold image. apply in_app_iff. right. apply in_app_iff. left. apply (In_areas_cells_intro A (st_areas A) a _ Hain).
intros next. unfold area_cells. left. reflexivity. }
assert (Cctx : In (MCell (LCtx CTX_secret) 8 (if st_init_done A then VSec else VZ 0)) (image A)).
{ unfold image; apply in_app_iff; left; unfold ctx_cells; left; reflexivity. }
assert (Hinit : st_init_done A = true).
{ destruct (st_init_done A) eqn:Ei; [reflexivity|]. exfalso.
pose proof (inv_ctx HW) as IM. destruct IM as (_&_&_&_&_&_&_&_&_&_&_& IM0).
destruct (IM0 Ei) as (EM & _). unfold used_metas in Hum. rewrite EM in Hum. exact Hum. }
rewrite Hinit in Cctx.
assert (Emem' : ptr_addr L (am_mem am) = GLO + ko) by (unfold ptr_addr, loc_addr; rewrite Emem; subst GLO; reflexivity).
assert (PRES_G : forall x, GLO <= x < GLO + rg_len rg -> present mem x).
{ intros x Hx. pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ MR) _ (footprint_region_In A kr rg Hrg1 Hrgk Hrgl)) as F.
cbn [foot_ok fst snd loc_addr] in F. apply F. subst GLO. lia. }
assert (PRES_A : forall x, ALO + oa <= x < ALO + oa + 4096 -> present mem x).
{ intros x Hx. assert (In2 : In (LMem a, PGSZ) (footprint A)) by (right; apply in_app_iff; left; apply in_map_iff; exists a; auto).
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ MR) _ In2) as F.
cbn [foot_ok fst snd] in F. rewrite Ea in F. cbn [loc_addr] in F. apply F. subst ALO. unfold PGSZ. lia. }
subst v. unfold fv_of in *.
split; cbn [fv_regs fv_g fv_mem fv_off fv_h3 fv_idx fv_rsv fv_bits fv_av fv_fr fv_area fv_sc fv_scl fv_last fv_ml fv_end fv_pn fv_glo fv_ghi fv_sec];
rewrite ?EP, ?Eg', ?Ea', ?Eend, ?Emem', ?Emem; cbn [prid poff]; rewrite <- ?EGLO, <- ?EPdef.
-   rewrite Eh3, meta_bits_enc.
pose proof (bits_nonneg (am_last am) (am_sc am) (am_maplen am)) as B0. pose proof (bits_lt64 (am_last am) (am_sc am) (am_maplen am)) as B1.
assert (SCL : 0 <= scl_of (am_sc am) <= 8191) by (unfold scl_of; destruct (am_sc am <? 48) eqn:E; [apply Z.ltb_lt in E; pose proof (scl_range (am_sc am)); lia | lia]).
destruct Hrc as (Hrc1 & _ & _).
pose proof (mc_sec _ _ _ _ _ MR) as SECR.
clear - Hrc1 B0 B1 SCL Hrsv Hoff16 H16 Hav32 Hfr32 Hsc Glast Gav Gfrn Hml51 Gml Bf P1 P2 Of Nf Ho R4096 Rceil HCE Hidx A4096 Hoa2 Hka Sp Hext Efp SECR.
repeat split; lia.
-   unfold fv_sp. cbn [fv_regs]. unfold spZ, ALLOC_STACK, CEIL in *.
split; [| exact Hsp16]. clear - Hsplo Hsphi. exact (conj Hsplo Hsphi).
-   split; [lia|]. rewrite EPdef. apply (mr_blocks_aligned B1 (MRc B1) (MRc_laws B1) L A mem md _ _ MR Hin).
-   unfold CEIL.
generalize Rimg; clear - Ho Hext P1 P2 Of Nf Bf Efp R4096 Rceil Hrsv Hpm Hoff16 Sp Hidx Glast; intros Rimg.
repeat (split; [lia|]). intros x Hx Hi. apply (Rimg x); [lia|]. apply in_img1_in_img. exact Hi.
-   unfold CEIL.
split; [lia|]. split; [lia|]. split.
{ rewrite Z.add_mod, Hoa, Z.add_0_r, Z.mod_mod by lia. unfold PGSZ in Aal. exact Aal. }
split; [lia|]. split; [lia|]. split; [| exact Hdisj].
intros x Hx Hi. apply (Aimg x); [subst ALO; lia|]. apply in_img1_in_img. exact Hi.
-   lia.
-   exact H16.
-   exact Hland.
-   lia.
-   apply meta_bits_enc.
- exact Hab.
- exact Hfb.
-   unfold kcase_of. destruct Hsc as [H63 | Hsc48].
+ rewrite H63. cbn [Z.eqb]. destruct Gcl as [(_ & Cl & Cml & _) | (C & _)]; [|lia].
split; [lia|]. split; [lia|]. split; [apply Hmlb; lia|]. split; [lia|]. split; [lia|].
assert (I0 : idx = 0) by lia. rewrite I0 in *. rewrite Z.mul_0_r in *.
rewrite EST. unfold stride_of. rewrite Cl. cbn [Z.eqb andb]. destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. cbn [negb]. unfold UNIT. lia.
+ replace (am_sc am =? 63) with false by (symmetry; apply Z.eqb_neq; lia).
destruct (Hscl ltac:(lia)) as [SR ->]. pose proof (Hclsb ltac:(lia)) as CB.
destruct (am_maplen am =? 0) eqn:Em0.
* apply Z.eqb_eq in Em0. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
rewrite EST. unfold stride_of. rewrite Em0. cbn [Z.eqb negb]. rewrite andb_false_r. unfold class_size, UNIT. lia.
* apply Z.eqb_neq in Em0. destruct (am_last am =? 0) eqn:El0.
-- apply Z.eqb_eq in El0. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply Hmlb; lia|]. split; [lia|]. split; [lia|].
assert (I0 : idx = 0) by lia. rewrite I0 in *. rewrite Z.mul_0_r in *.
rewrite EST. unfold stride_of. rewrite El0. cbn [Z.eqb andb]. replace (am_maplen am =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. unfold UNIT. lia.
-- apply Z.eqb_neq in El0. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [apply Hmlb; lia|]. split; [lia|].
rewrite EST. unfold stride_of. replace (am_last am =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. unfold class_size, UNIT. lia.
-   unfold rcase_of. destruct Hrc as (R1 & R2 & R3).
destruct (reserved_of am fr =? 0) eqn:E0; [apply Z.eqb_eq in E0; rewrite Eh3, R2; lia|]. apply Z.eqb_neq in E0.
destruct (reserved_of am fr <? 5) eqn:E5; [apply Z.ltb_lt in E5; rewrite Eh3, R2 by lia; repeat split; lia|]. apply Z.ltb_ge in E5.
destruct (reserved_of am fr =? 5) eqn:E55; [apply Z.eqb_eq in E55; rewrite Eh3, R3 by lia; repeat split; lia|]. apply Z.eqb_neq in E55.
rewrite Eh3, R3 by lia. repeat split; lia.
-   eapply bytes_are_at; [apply cell_bytes; apply CELL; exact C1 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
- eapply bytes_are_at; [apply cell_bytes; apply CELL; exact C2 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
- eapply bytes_are_at; [apply cell_bytes; apply CELL; exact C3 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
- eapply bytes_are_eq; [apply cell_bytes_ptr; apply CELL; exact C4 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia) | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
- eapply bytes_are_eq; [apply cell_bytes_ptr; apply CELL; exact C5 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia) | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
- eapply bytes_are_at; [apply cell_bytes; apply CELL; exact C6 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
- eapply bytes_are_at; [apply cell_bytes; apply CELL; exact C7 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
- eapply bytes_are_at; [apply cell_bytes; apply CELL; exact C8 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
-
eapply bytes_are_at; [apply cell_bytes_sec; apply CELL; exact Carea | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
-
assert (CB : bytes_are mem (loc_addr L (LCtx CTX_secret)) 8 (ly_sec L)).
{ apply cell_bytes_sec. apply CELL. exact Cctx. }
eapply bytes_are_at; [exact CB|]. unfold loc_addr. rewrite (mc_ctx _ _ _ _ _ MR). reflexivity.
- intros kk Hkk. destruct kk; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. exact (eq_trans (st_needlocks _ _ (mc_statics _ _ _ _ _ MR)) eq_refl).
-   unfold kcase_of. destruct Hsc as [H63 | Hsc48]; [rewrite H63; exact I|].
replace (am_sc am =? 63) with false by (symmetry; apply Z.eqb_neq; lia).
assert (TQ : bytes_are mem (TBL + 2 * am_sc am) 2 (scl_of (am_sc am))).
{ destruct (Hscl ltac:(lia)) as [SR ->].
destruct (so_size_classes _ SO (Z.to_nat (am_sc am)) ltac:(lia)) as (lo & hi & Hlo & Hhi & Hsum). rewrite Z2Nat.id in Hlo, Hhi by lia.
pose proof (u8_range lo). pose proof (u8_range hi).
pose proof (st_tables _ _ (mc_statics _ _ _ _ _ MR)) as STB. unfold table_addr in STB.
cbn [ms_segs ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt src0_msyms] in STB.
cbn [ms_segs ms_size_classes src0_msyms] in Hlo, Hhi. unfold w64 in STB, Hlo, Hhi.
unfold znth. rewrite <- Hsum.
intros kk Hkk. unfold TBL. rewrite STB by (unfold src0_D_size_classes, src0_D_debruijn32, src0_D_small_cnt_tab, src0_D_med_cnt_tab; lia).
destruct kk as [|[|]]; [| | lia]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
+ rewrite Z.add_0_r, Hlo. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 lo) at 1. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small _ 65536) by lia. rewrite (Z.mul_comm 256 (bv_unsigned hi)), Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
+ change (Z.of_nat 1) with 1. rewrite Hhi. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 hi) at 1. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 1) with 8.
rewrite (Z.mod_small _ 65536) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace ((bv_unsigned lo + 256 * bv_unsigned hi) / 256) with (bv_unsigned hi); [symmetry; apply Z.mod_small; lia|].
rewrite Z.add_comm. rewrite (Z.mul_comm 256 (bv_unsigned hi)). rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
destruct (am_maplen am =? 0); [exact TQ|]. destruct (am_last am =? 0); exact TQ.
-   destruct (Z.eq_dec idx (am_last am)) as [Eil | Nil].
+ assert (T0 : In (MCell (LMem (padd (am_mem am) (group_extent am))) 1 (VZ 0)) (tail_cells A)).
{ unfold tail_cells. apply in_flat_map. exists (g, am). split; [exact Hum|]. left. reflexivity. }
eapply bytes_are_at; [apply cell_bytes; apply TAIL; exact T0 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
+ destruct (slot_start_cells A g am (idx + 1) HW Hum ltac:(lia)) as [Cn _].
eapply bytes_are_at; [apply cell_bytes; apply CELL; exact Cn | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
-   unfold rcase_of. destruct (reserved_of am fr =? 0) eqn:E0; [exact I|]. destruct (reserved_of am fr <? 5) eqn:E5; [exact I|].
apply Z.ltb_ge in E5.
assert (TT : In (MCell (LMem (padd (slot_end am idx) (-4))) 4 (VZ (reserved_of am fr))) (tail_cells A) /\
In (MCell (LMem (padd (slot_end am idx) (-5))) 1 (VZ 0)) (tail_cells A)).
{ assert (FT : forall c, In c (frame_tail_cells am idx) -> In c (tail_cells A)).
{ intros c Hc. unfold tail_cells. apply in_flat_map. exists (g, am). split; [exact Hum|]. right. cbn [fst snd]. apply in_flat_map. exists idx. split; [apply (proj2 (In_zseq _ _ _)); lia | exact Hc]. }
unfold frame_tail_cells in FT. rewrite Hfr, Hk in FT. replace (5 <=? reserved_of am fr) with true in FT by (symmetry; apply Z.leb_le; lia).
split; apply FT; apply in_app_iff; right; cbn; auto. }
destruct TT as [T2 T3].
assert (G5 : bytes_are mem (GLO + ko + 16 + ST * idx + ST - 4 - 4) 4 (reserved_of am fr) /\ bytes_are mem (GLO + ko + 16 + ST * idx + ST - 4 - 5) 1 0 /\ P <= GLO + ko + 16 + ST * idx + ST - 4 - 5).
{ split; [|split; [|lia]].
- eapply bytes_are_at; [apply cell_bytes; apply TAIL; exact T2 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)].
- eapply bytes_are_at; [apply cell_bytes; apply TAIL; exact T3 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)]. }
destruct (reserved_of am fr =? 5); exact G5.
-   unfold rcase_of. destruct (reserved_of am fr =? 0) eqn:E0; [exact I|]. apply Z.eqb_neq in E0.
assert (T1 : In (MCell (LMem (padd (frame_ptr am idx fr) (fr_n fr))) 1 (VZ 0)) (tail_cells A)).
{ unfold tail_cells. apply in_flat_map. exists (g, am). split; [exact Hum|]. cbn [fst snd]. right. apply in_flat_map. exists idx. split; [apply (proj2 (In_zseq _ _ _)); lia |].
unfold frame_tail_cells. rewrite Hfr, Hk. replace (0 <? reserved_of am fr) with true by (symmetry; apply Z.ltb_lt; pose proof (proj1 Hrsv); lia).
apply in_app_iff. left. left. reflexivity. }
assert (GP : bytes_are mem (P + fr_n fr) 1 0).
{ eapply bytes_are_at; [apply cell_bytes; apply TAIL; exact T1 | (unfold ptr_addr, loc_addr, frame_ptr, slot_end, slot_start, group_extent, META_mem, META_avail, META_freed, META_bits, UNIT, IB; rewrite ?Emem, ?Eg, ?Ea; cbn [padd prid poff]; rewrite <- ?EGLO, <- ?EALO, <- ?EST; lia)]. }
destruct (reserved_of am fr <? 5); [exact GP|]. destruct (reserved_of am fr =? 5); [exact I | exact GP].
-   unfold rcase_of. destruct (reserved_of am fr =? 0) eqn:E0; [exact I|]. apply Z.eqb_neq in E0.
destruct (reserved_of am fr <? 5) eqn:E5; [apply Z.ltb_lt in E5; lia|]. apply Z.ltb_ge in E5.
destruct (reserved_of am fr =? 5) eqn:E55; [exact I|]. apply Z.eqb_neq in E55. lia.
-   intros x Hx. apply present_writable. apply PRES_G. lia.
-   intros x Hx. apply present_writable. apply PRES_A. lia.
-   intros x Hx. apply Hstk. unfold fv_sp in Hx. cbn [fv_regs] in Hx. unfold spZ, ALLOC_STACK. exact Hx.
Qed.
End e.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
