(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YG0b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG02 YG06 YG07 YG0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0l YG0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFhy AFhz AFi4 AFhm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFen.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFis AFi3 AFiy AFiz AFj0 AFix AFj2 AFiw AFiu AFit AFiv AFi5 AB13.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFkq AFkv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Lemma aview_eq_mbyte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
aview tfibsegs H' m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|]; cbn in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma val_mem_aview_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfibsegs H' m' (a + Z.of_nat k) = aview tfibsegs H m (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof. intros H H' m m' a n v HA Hv. eapply val_mem_ext; [|exact Hv]. intros k Hk. apply aview_eq_mbyte. exact (HA k Hk). Qed.
Lemma apresent_aview_some : forall (H : word -> bool) m a, TFIB_IMG_END <= a < 2 ^ 64 -> apresent H m a -> aview tfibsegs H m a <> None.
Proof.
intros H m a Ha Hp. destruct (apresent_mbyte H m a Hp) as [b Hb]. unfold aview. rewrite Hb. cbn. discriminate.
Qed.
Lemma aview_some_apresent : forall (H : word -> bool) m a, TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hv. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:E.
- exact (mbyte_high_apresent H m a b Ha E).
- exfalso. apply Hv. unfold aview. rewrite E. reflexivity.
Qed.
Lemma apresent_xfer : forall (H H' : word -> bool) m m' a, TFIB_IMG_END <= a < 2 ^ 64 ->
aview tfibsegs H' m' a = aview tfibsegs H m a -> apresent H m a -> apresent H' m' a.
Proof.
intros H H' m m' a Ha E Hp. apply aview_some_apresent; [exact Ha|]. rewrite E. exact (apresent_aview_some H m a Ha Hp).
Qed.
Lemma val_mem_aview : forall (H : word -> bool) m a (w : nat) v k, val_mem tfibsegs (mrestrict H m) a w v -> (k < w)%nat ->
aview tfibsegs H m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
intros H m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal.
apply unsigned_lit_small8. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma subregion_refl : forall r, subregion r r.
Proof. intros r. unfold subregion. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|]. intros c Hc; exact Hc. Qed.
Lemma region_kept_view : forall (H H' : word -> bool) (E : env) (m m' : word -> option byte) n lo hi wlo whi cs spv,
bv_unsigned (ew E n) = spv ->
(forall a, spv + lo <= a < spv + hi -> aview tfibsegs H' m' a = aview tfibsegs H m a) ->
TFIB_IMG_END <= spv + lo -> spv + hi <= 2 ^ 64 -> (forall a, spv + wlo <= a < spv + whi -> spv + lo <= a < spv + hi) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H' m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros H H' E m m' n lo hi wlo whi cs spv Hn HA Hlo Hhi Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply aview_eq_mbyte. apply HA. exact Ha.
- intros Hwr. pose proof (Hw a Ha) as Ha'. apply apresent_writable; [lia|]. apply (apresent_xfer H H' m m' a); [lia | apply HA; lia |].
apply writable_high_apresent; [lia | exact Hwr].
Qed.
Lemma extent_disjoint_sub : forall E r0 r r', YP09.r_base r' = YP09.r_base r0 -> YP09.r_lo r0 <= YP09.r_lo r' -> YP09.r_hi r' <= YP09.r_hi r0 ->
YP09.r_lo r' <= YP09.r_hi r' -> extent_disjoint E r0 r -> extent_disjoint E r' r.
Proof. intros E r0 r r' Hb Hlo Hhi Hwf H. unfold extent_disjoint in *. rewrite Hb. lia. Qed.
Lemma aowned_regs_only : forall B ly S S' a, regs_only S S' -> aowned B ly S' a <-> aowned B ly S a.
Proof.
intros B ly S S' a (Rck & Rsecs & _ & _ & _ & _ & Rfs & _). unfold aowned, aclient_byte, sec_extents, frames. rewrite Rck, Rfs. tauto.
Qed.
Lemma aowned_tick : forall B ly S a, aowned B ly (set_nev (st_nev S + 1) S) a <-> aowned B ly S a.
Proof. intros B ly S a. unfold aowned, aclient_byte, sec_extents, frames. cbn. tauto. Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. apply same_io_with_vm_backing. Qed.
Lemma E0_nondummy : forall ly regs0 n ch cl csz kz cnt v j0 jb j1 j2 j3 j4 cnt' v' j0' jb' j1' j2' j3' j4' k, (k < 64)%nat -> PND k = true ->
ew (AFis.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz) k = ew (AFis.E0 ly regs0 n ch cl cnt' v' csz j0' jb' j1' j2' j3' j4' kz) k.
Proof.
intros until k. intros Hk HP.
do 64 (destruct k as [|k]; [first [reflexivity | discriminate HP] |]). lia.
Qed.
Section e.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis D1 : tfib_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly 0x52bcc regs0 ch.
Hypothesis PRE : acall_pre tfibsegs B ly S W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange0 : 49 <= n <= 64512.
Hypothesis Htr : In tr (as_universe B).
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Hypothesis Hmiss : pc_chunks (cache S (chunk_class n)) = [].
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let cl : Z := chunk_class n.
Let kz : Z := rz_log n.
Let csz : Z := class_size cl.
Let mat0 : list word := m_vm_materialized md0.
Let md0' : list word -> Model := fun mat => with_vm_backing (m_vm_lazy md0) mat md0.
Let E0m : env := AFis.E0 ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0 kz.
Let DPOSTm : Z -> (word -> option byte) -> Prop := fun z m => AFix.DPOST3 W ly regs0 ch B S1 z m.
Lemma HAR0 : AR tfibsegs B ly S W mem0 md0. Proof. exact (proj1 PRE). Qed.
Lemma HARm0 : ARm B ly S (aview tfibsegs (w_H W) mem0). Proof. exact (proj1 HAR0). Qed.
Lemma Hev : aregime S. Proof. exact (proj1 (proj2 PRE)). Qed.
Lemma HAR1 : AR tfibsegs B ly S1 W mem0 md0. Proof. exact (AR_tick B ly S W mem0 md0 HAR0 Hev). Qed.
Lemma HARm1 : ARm B ly S1 (aview tfibsegs (w_H W) mem0). Proof. exact (proj1 HAR1). Qed.
Lemma LY : layout_ok ly. Proof. exact (am_layout _ _ _ _ HARm0). Qed.
Lemma IMG : img_cover ly. Proof. exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR0))). Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite (am_tsd _ _ _ _ HARm0). exact (ts_tsd B TS). Qed.
Lemma Htp : getr regs0 4 = w64 TFIB_TP.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp' & _). rewrite (ts_tp B TS) in Htp'. exact Htp'. Qed.
Lemma Hgp : getr regs0 3 = w64 (as_gp B). Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma Hra : YK0s.ret_ok (getr regs0 1). Proof. destruct PRE as (_ & _ & H & _). exact H. Qed.
Lemma Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Proof. destruct PRE as (_ & _ & _ & Hal & Hlo & Hbot & Hhi & _). unfold spZ in *. repeat split; assumption. Qed.
Lemma Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma HQT : qmeter S. Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
Lemma Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [H _] & _). exact H. Qed.
Lemma Hch : if sp0 + 16 <? ly_top ly
then if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch
else ch = [].
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ H] & _). unfold frame0_ok, spZ, s0Z in H. exact H. Qed.
Lemma Hkz : 1 <= kz <= 6 /\ rz_lo kz <= n <= rz_hi kz.
Proof.
subst kz. unfold rz_log. clear - Nrange0.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [cbn; lia|]. destruct (Z.leb_spec n 448); [cbn; lia|].
destruct (Z.leb_spec n 3968); [cbn; lia|]. destruct (Z.leb_spec n 16128); [cbn; lia|]. destruct (Z.leb_spec n 32256); [cbn; lia|].
destruct (Z.leb_spec n 64512); [cbn; lia|]. lia.
Qed.
Lemma Hkz1 : 1 <= kz <= 6. Proof. exact (proj1 Hkz). Qed.
Lemma Nrange : rz_lo kz <= n <= rz_hi kz. Proof. exact (proj2 Hkz). Qed.
Lemma Hcl_class : cl = chunk_class n. Proof. reflexivity. Qed.
Lemma Hcl : 1 <= cl <= 31. Proof. exact (@AFiy.Hcl' ly regs0 mem0 n cl 0 kz DPOSTm Hkz1 Nrange [] 0 Hcl_class). Qed.
Lemma Hcl_def : cl = class_id (AFis.R8v n + AFis.RZ kz).
Proof. pose proof (@AFis.casek_sizes n kz Hkz1 Nrange) as (L & RS & R8 & NP & FP & NS & RQ). subst cl. unfold chunk_class. rewrite NS, <- RS. reflexivity. Qed.
Lemma FP : from_primary n = true. Proof. pose proof (@AFis.casek_sizes n kz Hkz1 Nrange) as (_ & _ & _ & _ & FP' & _). exact FP'. Qed.
Lemma Hmiss1 : pc_chunks (cache S1 cl) = []. Proof. exact Hmiss. Qed.
Lemma Hvd : 0 <= 0 /\ 16 * 0 + 2 ^ 16 <= 2 ^ 32. Proof. lia. Qed.
Lemma Hcntd : 1 <= 1 <= 16. Proof. lia. Qed.
Lemma Hjbd : 0 <= 0 <= 255. Proof. lia. Qed.
Lemma Hv2d : 0 mod 2 = 0. Proof. reflexivity. Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. unfold sp0. apply u64_range. Qed.
Lemma STK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. pose proof (lo_top ly LY) as (_ & _ & _ & H4 & _ & _ & H7). split; [exact H7 | exact H4]. Qed.
Lemma WfP1 : WfP (as_universe B) 1 1 1 S1. Proof. exact (WfP_tick _ S (am_wf _ _ _ _ HARm0) Hev). Qed.
Lemma SEEDM : st_ok tfibsegs E0m MS0 (restrict (w_H W) (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs))).
Proof.
exact (@AFiw.SEEDM_ok _ _ W ly regs0 mem0 n ch cl 1 0 csz 0 0 0 0 0 0 kz Hcl Hvd Hcntd Hjbd Hv2d LY IMG Hn Htp Hsp DPOSTm Hkz1 Nrange B S1 TS HTSD HARm1 Hpres0 Hmiss1).
Qed.
Lemma MISS1 : SRr tfibsegs W (cfg_at tfibsegs 0x52930 regs0 mem0 md0) (AFiu.at_STM W ly regs0 mem0 md0 n ch cl 1 0 csz 0 0 0 0 0 0 kz MS_CALL).
Proof.
replace (cfg_at tfibsegs 0x52930 regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs)) (md0' mat0))
by (unfold cfg_at, md0', mat0; rewrite with_vm_backing_id; reflexivity).
exact (@AFiu.miss1 _ _ W ly regs0 mem0 md0 n ch cl 1 0 csz 0 0 0 0 0 0 kz Hcl Hvd Hcntd Hjbd Hv2d LY IMG Hn Hra4096 Hsp Hch DPOSTm Hkz1 Nrange Hcl_def mat0 U1 [] 0 SEEDM).
Qed.
Section f.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfibsegs Em MS_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ AFiu.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).
Lemma ms1_shape : ms1 = mkst (ms_regs ms1) (w64 0x36104) (ms_mem ms1) (seg_rom tfibsegs).
Proof. exact (st_ok_restrict_mkst tfibsegs (w_H W) Em _ _ HSC eq_refl). Qed.
Lemma HSC' : st_ok tfibsegs Em MS_CALL (mkst (ms_regs ms1) (w64 0x36104) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfibsegs)).
Proof. pose proof HSC as H. rewrite ms1_shape in H. exact H. Qed.
Lemma Em2 : ew Em 2 = getr regs0 2. Proof. rewrite (HEm 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em3 : ew Em 3 = getr regs0 3. Proof. rewrite (HEm 3%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em10 : ew Em 10 = getr regs0 10. Proof. rewrite (HEm 10%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em32 : ew Em 32 = w64 T. Proof. rewrite (HEm 32%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em39 : ew Em 39 = w64 cl. Proof. rewrite (HEm 39%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma Em40 : ew Em 40 = w64 (AFis.Pv ly cl). Proof. rewrite (HEm 40%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma T_range : zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL.
Proof. pose proof (@AFis.high_facts _ ly regs0 mem0 n 0 kz Hvd LY IMG DPOSTm) as (F1 & F2 & _). split; assumption. Qed.
Lemma R_ra : getr (ms_regs ms1) 1 = w64 0x35c64. Proof. rreg HSC (1%bv : bv 5) R. exact R. Qed.
Lemma R_sp : getr (ms_regs ms1) 2 = w64 (sp0 - 2320).
Proof. rreg HSC (2%bv : bv 5) R. rewrite R, Em2. unfold w64, sp0. f_equal; lia. Qed.
Lemma R_gp : getr (ms_regs ms1) 3 = getr regs0 3. Proof. rreg HSC (3%bv : bv 5) R. rewrite R, Em3. reflexivity. Qed.
Lemma R_tp : getr (ms_regs ms1) 4 = w64 TFIB_TP. Proof. rreg HSC (4%bv : bv 5) R. exact R. Qed.
Lemma R_a0 : getr (ms_regs ms1) 10 = w64 (T + t_cache).
Proof. rreg HSC (10%bv : bv 5) R. rewrite R, Em32. unfold w64, t_cache. rewrite Zbv_add_unsigned. reflexivity. Qed.
Lemma R_a1 : getr (ms_regs ms1) 11 = w64 (T + t_cache + 80 * cl). Proof. rreg HSC (11%bv : bv 5) R. rewrite R, Em40. reflexivity. Qed.
Lemma R_a2 : getr (ms_regs ms1) 12 = w64 A_ALLOCATOR. Proof. rreg HSC (12%bv : bv 5) R. exact R. Qed.
Lemma R_a3 : getr (ms_regs ms1) 13 = w64 cl. Proof. rreg HSC (13%bv : bv 5) R. rewrite R, Em39. reflexivity. Qed.
Lemma SP1 : spZ (ms_regs ms1) = sp0 - 2320.
Proof. unfold spZ. rewrite R_sp. unfold w64. apply unsigned_lit_small. pose proof Usp. pose proof Hsp. pose proof STK. unfold ASTACK, kHighMemBeg in *. lia. Qed.
Lemma UNW1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (T + t_unwinding) 1 0.
Proof.
pose proof T_range as [T1 T2].
memv HSC 41%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite Em32; unfold w64, t_unwinding; rewrite unsigned_lit_small by (ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); reflexivity
| reflexivity | cbn; lia].
Qed.
Lemma CNT1 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (AFis.Pv ly cl) 4 0.
Proof.
pose proof T_range as [T1 T2]. pose proof Hcl.
memv HSC 44%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite Em40; unfold w64, AFis.Pv, t_cache; rewrite unsigned_lit_small by (ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; lia); lia
| reflexivity | cbn; lia].
Qed.
Lemma UNW_cell : forall Sx rd, ARm B ly Sx rd -> rd (T + t_unwinding) = Some 0.
Proof.
intros Sx rd M. assert (IN : In (z1 (AT t_unwinding) 0) (acells B ly Sx)).
{ unfold acells. repeat (apply in_app_iff; right). left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (am_cells _ _ _ _ M) _ IN 0%nat ltac:(cbn; lia)) as X. cbn [c_at c_w aeval z1 c1] in X.
rewrite Z.add_0_r in X. exact X.
Qed.
Lemma AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem0 a.
Proof.
intros a Ha Hs. destruct (Z.eq_dec a (T + t_unwinding)) as [->|Hne].
- rewrite (UNW_cell S1 _ HARm1). pose proof (val_mem_aview (w_H W) (ms_mem ms1) (T + t_unwinding) 1 0 0 UNW1 ltac:(lia)) as X.
rewrite Z.add_0_r in X. rewrite X. reflexivity.
- apply aview_same. apply MEQW. rewrite unsigned_lit_small by exact Ha. unfold AFiu.WINM. fold sp0. unfold T in Hne. clear - Hs Hne. lia.
Qed.
Lemma AR1 : AR tfibsegs B ly S1 W (ms_mem ms1) (md0' mat1).
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof T_range as [T1 T2].
apply (AR_frame_law_ok tfibsegs B ly S1 W mem0 md0 (ms_mem ms1) (md0' mat1) HAR1).
- intros a Ha Ho. apply AG1; [exact Ha|]. intros Hst. apply (AR_stack_law_ok tfibsegs B ly S1 W mem0 md0 a HAR1); [|exact Ho].
clear - Hst Hlo Hhi. unfold ASTACK in *. lia.
- intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (AV : forall m, aview tfibsegs (w_H W) m a = aview tfibsegs (w_H W) m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
destruct (Z_lt_le_dec a' (sp0 - ASTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a' sp0) as [H2|H2]].
2:{ apply apresent_aview_some; [clear - H1 H2 K1 Ha' Hlo; unfold TFIB_IMG_END, kHighMemBeg, ASTACK in *; lia | apply PRESW; lia]. }
all: rewrite (AG1 a' Ha' ltac:(lia)); exact Hv.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Ha Hx. rewrite (MEQW (w64 a)); [reflexivity|].
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
unfold w64. rewrite unsigned_lit_small by exact Ha'. unfold AFiu.WINM. fold sp0.
pose proof (zone3_apart_hsh _ _ a T1) as TH. unfold T in TH. clear - Ha K1 Hlo TH.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, kThreadObjSize in *. lia.
Qed.
Lemma REFILL_PRE : refill_pre B ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof HAR0 as (_ & _ & [BUD _] & _).
unfold refill_pre. rewrite SP1. unfold raZ. rewrite R_ra, R_gp, R_tp, R_a0, R_a1, R_a2, R_a3, Hgp, (ts_tp B TS).
split; [exact AR1|].
split; [unfold abudget in *; cbn [st_nev set_nev S1]; change (sec_live_bytes S1) with (sec_live_bytes S); change (sec_hulls S1) with (sec_hulls S)  ; unfold EV_A in *; lia|].
split; [split; [pose proof (wf_prim_ev _ _ _ _ _ WfP1) as PE; cbn [st_nev set_nev S1] in PE |- *; change (prim_user_mapped S1) with (prim_user_mapped S) in *; lia|];
split; [exact (aregime_preg_tick S cl Hev Hcl) | exact (aregime_mid_tick S Hev)]|].
split; [split; [apply qtight_qloose; exact (qmeter_tight _ HQT) | apply (rroom_tick S); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact (qmeter_room _ HQT)]]|].
split; [apply ret_ok_even; reflexivity|]. split; [unfold w64; rewrite unsigned_lit_small by lia; lia|].
split; [clear - Hal; replace (sp0 - 2320) with (sp0 + (-145) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [clear - Hlo; unfold ASTACK, RSTACK in *; lia|]. split; [lia|].
split; [intros a Ha; apply PRESW; clear - Ha; unfold ASTACK, RSTACK in *; lia|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hcl | exact Hmiss1].
Qed.
Section g.
Variables (S' : astate) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis WFP' : WfP (as_universe B) 0 1 1 S'.
Hypothesis RO : regs_only S1 S'.
Hypothesis CI : st_cache_inited S' = true.
Hypothesis POST : acall_post tfibsegs B RSTACK ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR.
Let msR : machine_state := mkst regsR (w64 0x35c64) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Lemma HAR' : AR tfibsegs B ly S' W' memR mdR. Proof. exact (proj1 POST). Qed.
Lemma HARm' : ARm B ly S' (aview tfibsegs (w_H W') memR). Proof. exact (proj1 HAR'). Qed.
Lemma WLE : wle W W'. Proof. exact (proj1 (proj2 (proj2 POST))). Qed.
Lemma ERRNO_low : as_errno B + 4 <= kHighMemBeg.
Proof. rewrite (ts_errno B TS). unfold TFIB_ERRNO, kHighMemBeg. lia. Qed.
Lemma AGR : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2320 - RSTACK <= a < sp0 - 2320) ->
aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a.
Proof.
intros a Ha Hns. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof ERRNO_low as EL.
destruct POST as (_ & _ & _ & _ & _ & FR & _). apply FR.
- clear - Ha Hlo K1 U. unfold ASTACK, kHighMemBeg in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S1 W (ms_mem ms1) (md0' mat1) a AR1). clear - Ha Hlo Hhi. unfold ASTACK in *. lia.
- apply (AR_stack_law_ok tfibsegs B ly S' W' memR mdR a HAR'). clear - Ha Hlo Hhi. unfold ASTACK in *. lia.
- unfold ascratch. rewrite SP1. intros [X|X]; [exact (Hns X)|]. clear - X Ha Hlo K1 EL. unfold ASTACK, kHighMemBeg in *. lia.
- intros [].
Qed.
Lemma PRES' : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
assert (Hhi' : TFIB_IMG_END <= a < 2 ^ 64) by (clear - Ha Hlo K1 U; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia).
destruct (Z_lt_le_dec a (sp0 - 2320 - RSTACK)) as [H1|H1]; [|destruct (Z_lt_le_dec a (sp0 - 2320)) as [H2|H2]].
- apply (apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [apply AGR; [exact Ha | lia] | apply PRESW; exact Ha].
- destruct POST as (_ & _ & _ & _ & _ & _ & PRS). apply PRS. rewrite SP1. lia.
- apply (apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [apply AGR; [exact Ha | lia] | apply PRESW; exact Ha].
Qed.
Lemma BUF' : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W') memR) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).
Proof.
intros i Hi. pose proof (@AFis.tr_length ly regs0 mem0 n ch 0 kz DPOSTm) as LEN. change (AFis.tr ly regs0 ch) with tr in LEN.
eapply val_mem_aview_xfer; [|exact (BUFW i Hi)]. intros k Hk. apply AGR; clear - Hi Hk LEN; unfold IFRAME, ASTACK, RSTACK in *; lia.
Qed.
Let E1 : env := havoc Em hRF (map (getr regsR) CLOB).
Lemma Em2u : bv_unsigned (ew Em 2) = sp0. Proof. rewrite Em2. reflexivity. Qed.
Lemma KEPT3 : Forall (region_kept tfibsegs Em (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W') memR)) RS3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
assert (A : forall a, sp0 - 2320 <= a < sp0 -> aview tfibsegs (w_H W') memR a = aview tfibsegs (w_H W) (ms_mem ms1) a)
by (intros a Ha; apply AGR; clear - Ha; unfold ASTACK, RSTACK; lia).
unfold RS3. repeat (apply Forall_cons; [eapply (region_kept_view (w_H W) (w_H W') Em (ms_mem ms1) memR 2 _ _ _ _ _ sp0 Em2u);
[intros a Ha; apply A; clear - Ha; lia | clear - Hlo K1; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia | clear - U; lia | clear; intros a Ha; lia] |]).
apply Forall_nil.
Qed.
Let ms3 : machine_state := mkst regsR (w64 0x35c64) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Lemma HS3 : st_ok tfibsegs E1 SS3 ms3.
Proof.
rewrite SS3_eq. pose proof MS_CALL_facts as (F1 & F2 & F3 & F4 & F5 & F6). destruct MS_CALL_mem3 as [rest ER].
apply (st_ok_after_call tfibsegs hRF Em MS_CALL (mkst (ms_regs ms1) (w64 0x36104) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfibsegs))
regsR (mrestrict (w_H W') memR) RS3 0x35c64 HSC' F6 F1 F2 F3 F4).
- rewrite ER. change RS3 with [R3bst; trim_lo R3scr (-2320); R3top].
apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_trim_lo|]. apply submem_keep; [apply subregion_refl|]. apply submem_nil.
- exact F5.
- destruct POST as (_ & _ & _ & CS & _). intros r Hr. apply CS. exact Hr.
- exact KEPT3.
Qed.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA0 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => AFix.DPOST3 W' ly regs0 ch B S' z m.
Lemma Hcnt_def' : cnt' = Z.of_nat (length (l ++ [off])). Proof. reflexivity. Qed.
Lemma Hcsz_def : csz = class_size cl. Proof. reflexivity. Qed.
Lemma Hoffv' : off = 16 * v' /\ v' mod 2 = 0.
Proof.
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm') cl Hcl) as CL. pose proof (wr_elems _ _ _ _ _ _ CL) as EL. rewrite Hcache' in EL.
pose proof (proj1 (Forall_forall _ _) EL off ltac:(rewrite !in_app_iff; cbn; tauto)) as [_ O2].
pose proof (class_ok cl Hcl) as (K1 & K2 & _). apply Z.mod_divide in O2 as [q Hq]; [|lia]. apply Z.mod_divide in K2 as [r Hr]; [|lia].
subst v'. rewrite Hq, Hr. replace (q * (r * 32)) with ((2 * q * r) * 16) by lia. rewrite Z.div_mul by lia. split; [lia|].
rewrite <- Z.mul_assoc, Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma Hoff_def' : off = 16 * v'. Proof. exact (proj1 Hoffv'). Qed.
Lemma Hv2' : v' mod 2 = 0. Proof. exact (proj2 Hoffv'). Qed.
Lemma Hv' : 0 <= v' /\ 16 * v' + 2 ^ 16 <= 2 ^ 32.
Proof. exact (@AFiy.Hv' _ W' ly regs0 memR n cl cnt' v' kz Hv2' DPOST' Hkz1 Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def'). Qed.
Lemma Hcnt' : 1 <= cnt' <= 16.
Proof. exact (@AFiy.Hcnt' _ W' ly regs0 memR n cl cnt' v' kz Hv2' Hsp DPOST' Hkz1 Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def'). Qed.
Variables (j0 jb j1 j2 j3 j4 : Z).
Let Kv' : Z := AFis.Kv ly cl v'.
Let RZ : Z := AFis.RZ kz.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W') memR) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W') memR) (AFis.SSLOTv ly cl) 8 j4.
Hypothesis Hjb : 0 <= jb <= 255.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W') memR) (Kv' + RZ - 15) 1 jb.
Let E0' : env := AFis.E0 ly regs0 n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz.
Let Es : env := env_merge PND E1 E0'.
Lemma HEs : forall k, (k < aHAV)%nat -> ew Es k = ew E0' k.
Proof.
intros k Hk. unfold aHAV in Hk. destruct (PND k) eqn:HP.
- unfold Es. rewrite (ew_merge_in PND E1 E0' k HP). unfold E1. rewrite ew_havoc_old by (unfold hRF; lia).
rewrite (HEm k Hk). unfold E0m, E0'. apply E0_nondummy; [exact Hk | exact HP].
- unfold Es. apply ew_merge_out. exact HP.
Qed.
Lemma AGs : env_agree 64 E0' Es.
Proof. split; [exact HEs | reflexivity]. Qed.
Lemma Es2 : bv_unsigned (ew Es 2) = sp0. Proof. rewrite (HEs 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma FACTS' : atoms_ok E0' (f_atoms FG).
Proof.
exact (@AFj0.FACTS_ok _ W' ly regs0 memR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hn Hsp DPOST' Hkz1 Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def).
Qed.
Lemma REG0' : Forall (region_ok tfibsegs E0' (mrestrict (w_H W') memR)) REG0.
Proof.
exact (@AFiz.REG0_ok _ W' ly regs0 memR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hsp DPOST' Hkz1 Nrange B S' l off TS HTSD HARm' PRES' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Qed.
Lemma PAIRS' : pairwise_disjoint E0' REG0.
Proof.
exact (@AFj0.PAIRS_ok _ W' ly regs0 memR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hv2' LY IMG Hsp DPOST' Hkz1 Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def).
Qed.
Lemma HS4 : st_ok tfibsegs Es SS3 ms3.
Proof.
pose proof SS3_atoms as (A1 & A2 & A3 & A4 & A5). pose proof tlREG0_facts as (_ & _ & T3).
apply (st_ok_agree_on2 tfibsegs PND E1 Es SS3 ms3 HS3 (env_merge_on PND E1 E0') A1 A2 A3 A4).
rewrite A5. exact (atoms_ok_agree 64 E0' Es _ AGs T3 FACTS').
Qed.
Lemma HS5 : st_ok tfibsegs Es (mkSS (ss_pc SS3) (sr_set (ss_regs SS3) 10%bv (SLit 1)) (ss_mem SS3) (ss_resv SS3) (ss_facts SS3)) ms3.
Proof.
apply (st_ok_pin_regU Es SS3 ms3 10%bv (SLit 1) HS4); [intros X; discriminate X|].
pose proof (st_ok_reg tfibsegs Es SS3 ms3 10%bv HS4) as R. unfold U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. reflexivity.
Qed.
Lemma region_ok_agree_on_lt : forall r, In r (tl REG0) -> region_ok tfibsegs E0' (mrestrict (w_H W') memR) r -> region_ok tfibsegs Es (ms_mem ms3) r.
Proof.
intros r Hr H. pose proof tlREG0_facts as (T1 & _). unfold ms3. cbn [ms_mem mkst].
apply (region_ok_agree tfibsegs 64 E0' Es _ r AGs); [|exact H]. exact (proj1 (forallb_forall _ _) T1 r Hr).
Qed.
Lemma HS6 : st_ok tfibsegs Es (mkSS 0x35c64 (sr_set (ss_regs SS3) 10%bv (SLit 1)) [R3bst; R3scr; R3top] None (ss_facts SS3)) ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
pose proof (st_ok_mem_surgery Es _ ms3 [R3bst; R3scr; R3top] HS5) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val Es (Some 2%nat) = sp0) by (cbn [base_val]; exact Es2).
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons; [|exact (Forall_inv_tail (Forall_inv_tail HF))].
pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, R3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
split; [clear - Hlo K1; unfold ASTACK, kHighMemBeg in *; lia|]. split; [clear - U; lia|]. split; [|exact R4].
intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 U; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia|]. apply PRES'. clear - Ho; unfold ASTACK; lia.
- unfold R3bst, R3scr, R3top. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV. repeat split; lia.
Qed.
Lemma HS7 : st_ok tfibsegs Es MS_AFTER ms3.
Proof.
rewrite MS_AFTER_eq3. pose proof tlREG0_facts as (T1 & T2 & T3).
pose proof (st_ok_mem_surgery Es _ ms3 ([R3bst; R3scr; R3top] ++ tl REG0) HS6) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X.
intros HM. pose proof PAIRS' as PP. change REG0 with (hd R_bst REG0 :: tl REG0) in PP. destruct PP as [A0 PT].
pose proof REG0' as RR. change REG0 with (hd R_bst REG0 :: tl REG0) in RR. apply Forall_inv_tail in RR.
apply mem_ok_app; [exact HM | exact T2 | | |].
- apply Forall_forall. intros r Hr. apply (region_ok_agree_on_lt r Hr). exact (proj1 (Forall_forall _ _) RR r Hr).
- exact (pairwise_disjoint_agree 64 E0' Es (tl REG0) AGs T1 PT).
- intros r Hr. pose proof (all_disjoint_In E0' _ _ r A0 Hr) as D0.
assert (Hb : obase_lt 64 (YP09.r_base r) = true).
{ pose proof (proj1 (forallb_forall _ _) T1 r Hr) as Ha. unfold region_atoms_lt in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
pose proof (extent_disjoint_agree 64 E0' Es (hd R_bst REG0) r AGs eq_refl Hb D0) as D. clear D0.
cbn [all_disjoint]. repeat split; apply extent_disjoint_sym;
(eapply (extent_disjoint_sub Es (hd R_bst REG0) r); [reflexivity | cbn; unfold ASTACK; lia | cbn; lia | cbn; lia | exact D]).
Qed.
Lemma ATJ : AFis.at_ST W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz MS_AFTER W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), Es. split; [reflexivity|]. split; [exact HEs|].
split; [unfold msR; rewrite restrict_mkst_fx; exact HS7|].
split; [intros x _; reflexivity|]. split; [exact PRES' | exact BUF'].
Qed.
Lemma HKpres' : forall a, Kv' <= a < Kv' + RZ + AFis.R8v n -> apresent (w_H W') memR a.
Proof. exact (@AFiy.KPRES _ W' ly regs0 memR n cl cnt' v' csz kz Hv2' LY Hsp DPOST' Hkz1 Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def). Qed.
Lemma HSKpres' : forall a, AFis.SKv ly cl v' <= a < AFis.SKv ly cl v' + (RZ + AFis.R8v n) / 8 -> apresent (w_H W') memR a.
Proof. exact (@AFiy.SKPRES _ W' ly regs0 memR n cl cnt' v' csz kz Hv2' LY IMG Hsp DPOST' Hkz1 Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def). Qed.
Lemma HPB250' : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W') memR) (AFis.PBv ly n cl v' kz) 1 250.
Proof. exact (@AFiy.PB250 _ W' ly regs0 memR n cl cnt' v' csz kz Hv2' LY IMG Hsp DPOST' Hkz1 Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def). Qed.
Lemma SEED' : st_ok tfibsegs E0' SS0 (restrict (w_H W') (mkst regs0 (w64 0x52930) memR (seg_rom tfibsegs))).
Proof.
exact (@AFj0.SEED_ok _ _ W' ly regs0 memR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hn Htp Hsp DPOST' Hkz1 Nrange B S' l off TS HTSD HARm' PRES' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Qed.
Lemma TAILJ : amreal tfibsegs (malloc_join n tr cl S') W' (cfg_at tfibsegs 0x35c64 regsR memR mdR)
(fun r W'' c'' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S' W' regs0 memR mdR n r W'' c'').
Proof.
replace (cfg_at tfibsegs 0x35c64 regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply amreal_SRr_pre.
{ exact (@AFit.segJ _ _ W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hv2' LY IMG Hsp DPOST' Hkz1 Nrange l off W' cR ATJ). }
intros W2 c2 _ HJ. pose proof (proj1 HJ) as EW. subst W2.
exact (@AFj2.tail_inner _ _ W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 kz Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hn Htp Hra Hsp DPOST' HKpres' HSKpres' HPB250' Hkz1 Nrange Hcl_def (m_vm_materialized mdR) SEED' B S' l off TS HTSD HARm' Hgp CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def Hj4 Hjb_def Htr HAR' D1 (fun z m H => H) (fun z m H => H) c2 HJ).
Qed.
End g.
Lemma rw_writable : forall (m : word -> option byte) a, 0x9d000 <= a < 0x5fb000 -> writable_at tfibsegs m a.
Proof. intros m a Ha. unfold writable_at. apply AB13.tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha. Qed.
Lemma aview_rw_some : forall (Hh : word -> bool) m a, 0x9d000 <= a < 0x5fb000 -> aview tfibsegs Hh m a <> None.
Proof.
intros Hh m a Ha. unfold aview, mbyte. destruct (mrestrict Hh m (Z_to_bv 64 a)); cbn; [discriminate|].
pose proof (AB13.tfib_rw_rom a Ha) as X. destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | exfalso; exact (X eq_refl)].
Qed.
Section h.
Variables (S' : astate) (W' : world tfibsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis RO : regs_only S1 S'.
Hypothesis CI : st_cache_inited S' = true.
Hypothesis POST : acall_post tfibsegs B RSTACK ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR.
Hypothesis Hc0 : pc_chunks (cache S' cl) = [].
Hypothesis HA0 : getr regsR 10 = w64 0.
Let msR : machine_state := mkst regsR (w64 0x35c64) memR (seg_rom tfibsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Let ms3 : machine_state := mkst regsR (w64 0x35c64) (mrestrict (w_H W') memR) (seg_rom tfibsegs).
Let E1 : env := havoc Em hRF (map (getr regsR) CLOB).
Lemma HE1 : forall k, (k < aHAV)%nat -> ew E1 k = ew E0m k.
Proof. intros k Hk. unfold E1. unfold aHAV in Hk. rewrite ew_havoc_old by (unfold hRF; lia). apply HEm. exact Hk. Qed.
Lemma E1_2 : bv_unsigned (ew E1 2) = sp0. Proof. rewrite (HE1 2%nat ltac:(cbv; lia)). reflexivity. Qed.
Lemma HSN : st_ok tfibsegs E1 MS_N0 ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as Us.
pose proof (HS3 S' W' regsR memR mdR POST) as H3. fold E1 in H3. change (mkst regsR (w64 0x35c64) (mrestrict (w_H W') memR) (seg_rom tfibsegs)) with ms3 in H3.
assert (H4 : st_ok tfibsegs E1 (mkSS (ss_pc SS3) (sr_set (ss_regs SS3) 10%bv (SLit 0)) (ss_mem SS3) (ss_resv SS3) (ss_facts SS3)) ms3).
{ apply (st_ok_pin_regU E1 SS3 ms3 10%bv (SLit 0) H3); [intros X; discriminate X|].
pose proof (st_ok_reg tfibsegs E1 SS3 ms3 10%bv H3) as R. unfold U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. reflexivity. }
rewrite MS_N0_eq. pose proof (st_ok_mem_surgery E1 _ ms3 ([R3bst; R3scr; R3top] ++ NREGS) H4) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. apply X. clear X H4 H3.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val E1 (Some 2%nat) = sp0) by (cbn [base_val]; exact E1_2).
pose proof (PRES' S' W' regsR memR mdR POST) as PR.
assert (OOM1 : val_mem tfibsegs (mrestrict (w_H W') memR) (TFIB_OOM + 1) 1 1).
{ pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (HARm' S' W' regsR memR mdR POST)) (z1 (ANum (TFIB_OOM + 1)) 1)) as C.
rewrite (ts_const B TS ly) in C. specialize (C ltac:(unfold Tfib_const; apply in_app_iff; right; apply in_app_iff; left; apply (nth_error_In _ 60); reflexivity)).
exact (cell_holds_val_mem B ly (w_H W') memR (ANum (TFIB_OOM + 1)) 1 (ANum 1) C). }
split; [reflexivity|]. split.
- apply Forall_cons; [exact (Forall_inv HF)|]. apply Forall_cons.
{ pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, R3scr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV.
split; [clear - Hlo K1; unfold ASTACK, kHighMemBeg in *; lia|]. split; [clear - Us; lia|]. split; [|exact R4].
intros o Ho. apply apresent_writable; [clear - Ho Hlo K1 Us; unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *; lia|]. apply PR. clear - Ho; unfold ASTACK; lia. }
apply Forall_cons; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HF)))|].
unfold NREGS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ unfold region_ok, lit1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia |]. rewrite Z.add_0_l. exact OOM1.
+ unfold region_ok, oomR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; lia|]. split; [unfold TFIB_OOM; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply rw_writable. unfold TFIB_OOM in *. lia.
+ unfold region_ok, errR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_ERRNO; lia|]. split; [unfold TFIB_ERRNO; lia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply rw_writable. unfold TFIB_ERRNO in *. lia.
- unfold R3bst, R3scr, R3top, NREGS, lit1, oomR, errR. cbn [pairwise_disjoint all_disjoint app]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BV. cbn [base_val]. clear - Hlo K1 Us. unfold TFIB_OOM, TFIB_ERRNO, ASTACK, kHighMemBeg in *. repeat split; lia.
Qed.
Lemma ATN : AFiv.at_STN W' ly regs0 memR mdR n ch cl 1 0 csz 0 0 0 0 0 0 kz MS_N0 W' cR.
Proof.
split; [reflexivity|]. exists msR, (m_vm_materialized mdR), E1. split; [reflexivity|]. split; [exact HE1|].
split; [unfold msR; rewrite restrict_mkst_fx; exact HSN|]. split; [reflexivity | exact (PRES' S' W' regsR memR mdR POST)].
Qed.
Lemma errno_not_owned : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S' a.
Proof.
intros a Ha O. pose proof (HAR' S' W' regsR memR mdR POST) as AR'.
assert (IMGa : in_img tfibsegs a).
{ unfold in_img. rewrite AB13.tfib_segs_eq.
eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. lia. }
apply (proj1 (AR_owned_image_law_ok tfibsegs B ly S' W' memR mdR a AR' IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; lia|] | False => destruct Hr end.
Qed.
Lemma oom_owned : aowned B ly S' TFIB_OOM.
Proof.
apply (own_area B ly S' _ (as_oom_byte B, 1) TFIB_OOM (HARm' S' W' regsR memR mdR POST)); [unfold asyms_areas; cbn; tauto|].
cbn [fst snd]. rewrite (ts_oom B TS). lia.
Qed.
Lemma TAILN : amreal tfibsegs (malloc_join n tr cl S') W' (cfg_at tfibsegs 0x35c64 regsR memR mdR)
(fun r W'' c'' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W'' c'').
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as Us. pose proof ERRNO_low as EL.
unfold malloc_join. rewrite bind_assoc_eq. eapply amreal_pure; [exact (pop_miss S' cl Hc0)|]. eapply amreal_pure; [reflexivity|].
unfold malloc_K. cbn [amreal].
replace (cfg_at tfibsegs 0x35c64 regsR memR mdR) with cR by (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; reflexivity).
eapply SRr_mono.
{ exact (@AFiv.segN _ _ W' ly regs0 memR mdR n ch cl 1 0 csz 0 0 0 0 0 0 kz Hvd LY IMG Htp Hra Hsp DPOSTm [] 0 W' cR ATN). }
intros W6 c6 _ HR [WF' QT']. cbn [fst snd] in WF', QT' |- *.
destruct HR as (-> & regs' & mem' & mat & -> & A0 & CS' & MEQ' & PRS' & VOOM & VERR).
pose proof POST as (AR' & _ & WLE & CS & SIO & FR & _). pose proof (HARm' S' W' regsR memR mdR POST) as M'.
exists ly, regs', mem', (with_vm_backing (m_vm_lazy mdR) mat mdR).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [|split; [rewrite A0; cbn [sptr_addr sptr_exp aeval]; reflexivity | exact QT']].
assert (NWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> a <> TFIB_OOM -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) -> mem' (Z_to_bv 64 a) = memR (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3. apply MEQ'. rewrite unsigned_lit_small by exact Ra. unfold AFiv.WINN. fold sp0. clear - N1 N2 N3. unfold IFRAME, ASTACK in *. lia. }
split.
{
apply (AR_oom B ly S' W' memR mem' mdR (with_vm_backing (m_vm_lazy mdR) mat mdR) TS AR').
- intros a Ra Ho NX. apply aview_same. apply NWIN; [exact Ra | | clear - NX; unfold XJ in NX; lia |].
+ intros ST. exact (AR_stack_law_ok tfibsegs B ly S' W' memR mdR a AR' ltac:(clear - ST Hlo Hhi; unfold ASTACK in *; lia) Ho).
+ intros ER. exact (errno_not_owned a ER Ho).
- intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (AV : forall m, aview tfibsegs (w_H W') m a = aview tfibsegs (w_H W') m a') by (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
destruct (Z_le_gt_dec (sp0 - ASTACK) a') as [G1|G1]; [destruct (Z_lt_ge_dec a' sp0) as [G2|G2]|].
{ apply apresent_aview_some; [clear - G1 G2 K1 Ha' Hlo; unfold TFIB_IMG_END, kHighMemBeg, ASTACK in *; lia | apply PRS'; lia]. }
all: destruct (Z.eq_dec a' TFIB_OOM) as [->|NO]; [apply aview_rw_some; unfold TFIB_OOM; lia|].
all: destruct (Z_le_gt_dec TFIB_ERRNO a') as [G3|G3]; [destruct (Z_lt_ge_dec a' (TFIB_ERRNO + 4)) as [G4|G4]; [apply aview_rw_some; unfold TFIB_ERRNO in *; lia|]|].
all: rewrite (aview_same (w_H W') memR mem' a' (NWIN a' Ha' ltac:(lia) NO ltac:(lia))); exact Hv.
- apply m_vmmaps_wvb.
- apply m_vm_lazy_wvb.
- apply eager_used_wvb.
- intros a Ha Hx. unfold YG0n.w64. apply NWIN.
+ clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia.
+ clear - Ha K1 Hlo. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. lia.
+ clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_OOM in *. lia.
+ clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_ERRNO in *. lia. }
split; [apply layout_le_refl|].
split; [exact WLE|].
split.
{
intros r Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - RR CS'. repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst r; apply CS'; cbn [In];
repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_wvb md0 mat1) SIO) (same_io_wvb mdR mat))|].
split; [|exact PRS'].
intros a Ha NO NO' NS NE.
assert (NO1 : ~ aowned B ly S1 a) by (intros O; apply NO; exact (proj1 (aowned_tick B ly S a) O)).
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (intros X; apply NS; unfold ascratch, spZ; left; exact X).
assert (NER : ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4)) by (intros X; apply NS; unfold ascratch; right; rewrite (ts_errno B TS); exact X).
assert (NOO : a <> TFIB_OOM) by (intros ->; exact (NO' oom_owned)).
rewrite (aview_same (w_H W') memR mem' a (NWIN a Ha NST NOO NER)). rewrite (FR a Ha NO1 NO').
- exact (AG1 a Ha NST).
- unfold ascratch in NS |- *. rewrite SP1. unfold spZ in NS. fold sp0 in NS. intros [X|X]; apply NS; [left; clear - X; unfold ASTACK, RSTACK in *; lia | right; exact X].
- intros [].
Qed.
End h.
Lemma SHIFT : forall S' W' regsR memR mdR, regs_only S1 S' ->
acall_post tfibsegs B RSTACK ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR ->
forall r W6 c6, malloc_leaf tfibsegs B ly S' W' regs0 memR mdR n r W6 c6 -> malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n r W6 c6.
Proof.
intros S' W' regsR memR mdR RO POST r W6 c6 (ly' & regs' & mem' & md' & -> & AP & RA0 & QT).
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof ERRNO_low as EL.
destruct AP as (AR6 & LLE & WLE6 & CS6 & SIO6 & FR6 & PRS6). destruct POST as (AR' & _ & WLE & _ & SIO & FR & _).
exists ly', regs', mem', md'. split; [reflexivity|]. split; [|split; [exact RA0 | exact QT]].
split; [exact AR6|]. split.
{ destruct RO as (_ & Rsecs & _). rewrite Rsecs in LLE. exact LLE. }
split; [exact (wle_trans _ _ _ _ WLE WLE6)|]. split; [exact CS6|].
split; [exact (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_wvb md0 mat1) SIO) SIO6)|]. split; [|exact PRS6].
intros a Ha NO NO6 NS NE.
assert (NO1 : ~ aowned B ly S1 a) by (intros O; apply NO; exact (proj1 (aowned_tick B ly S a) O)).
assert (NO' : ~ aowned B ly S' a) by (intros O; apply NO1; exact (proj1 (aowned_regs_only B ly S1 S' a RO) O)).
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (intros X; apply NS; unfold ascratch, spZ; left; exact X).
rewrite (FR6 a Ha NO' NO6 NS NE). rewrite (FR a Ha NO1 NO').
- exact (AG1 a Ha NST).
- unfold ascratch in NS |- *. rewrite SP1. unfold spZ in NS. fold sp0 in NS. intros [X|X]; apply NS; [left; clear - X; unfold ASTACK, RSTACK in *; lia | right; exact X].
- intros [].
Qed.
End f.
Theorem malloc_missg :
amreal tfibsegs (malloc n tr S) W (cfg_at tfibsegs 0x52930 regs0 mem0 md0) (malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n).
Proof.
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) (am_wf _ _ _ _ HARm0) Hev); [unfold MALLOC_MAX; lia | exact Hlive | exact Htr]. }
rewrite (malloc_primary_eq n tr S FP). eapply amreal_pure; [reflexivity|].
eapply amreal_pure; [unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; lia); reflexivity|].
fold S1. change (chunk_class n) with cl.
eapply (YG0d.amreal_mbind tfibsegs (refill_tree cl) (fun _ : unit => malloc_join n tr cl) S1 W _
(fun r W' c' => exists ms1 mat1 Em,
((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfibsegs Em MS_CALL (restrict (w_H W) ms1) /\
(forall x : word, ~ AFiu.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
((WfP (as_universe B) (1 - 1) 1 1 (snd r) /\ regs_only S1 (snd r) /\ st_cache_inited (snd r) = true) /\
refill_leaf B ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl r W' c'))).
-
eapply amreal_SRr_pre; [exact MISS1|]. intros W1 c1 _ HC.
destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
pose proof (tfib_refill_ok B TS ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl (REFILL_PRE ms1 mat1 Em HEm HSC MEQW PRESW)) as RR.
unfold cfg_at, A_Refill in RR. rewrite (ms1_shape ms1 Em HSC) at 1. change (md0' mat1) with (with_vm_backing (m_vm_lazy md0) mat1 md0) in RR at 1.
pose proof (refill_tree_apost (as_universe B) 1 1 1 S1 cl WfP1 Hcl ltac:(lia) (aregime_preg_tick S cl Hev Hcl)) as APOST.
eapply amreal_mono; [| exact (amreal_apost tfibsegs _ _ W _ _ APOST RR)].
intros r W' c' H. exists ms1, mat1, Em. split; [|exact H]. repeat (split; [assumption|]). exact BUFW.
-
intros [] S' W' c' (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & (WFP' & RO & CI) & HL). cbn [fst snd] in WFP', RO, CI, HL.
destruct HL as (regsR & memR & mdR & -> & POST & HA0). cbn [snd] in HA0.
unfold raZ. rewrite (R_ra ms1 Em HSC). unfold w64 at 1. rewrite unsigned_lit_small by lia.
destruct (pc_chunks (cache S' cl)) as [|x t] eqn:El.
+
eapply amreal_mono; [| exact (TAILN ms1 mat1 Em HEm HSC MEQW PRESW S' W' regsR memR mdR POST El HA0)].
intros [p s6] W6 c6 H [ns MP]. cbn [fst snd] in H, MP. apply H. destruct MP as (WF' & _ & _ & _ & _ & QT). exact (conj WF' (QT (qmeter_tight _ HQT))).
+ assert (LX : exists l off, x :: t = l ++ [off]) by (exists (List.removelast (x :: t)), (List.last (x :: t) 0); apply List.app_removelast_last; discriminate).
destruct LX as (l & off & LX). rewrite LX in El.
destruct (@AFiy.junk_values _ W' ly regs0 memR n cl (Z.of_nat (length (l ++ [off]))) (off / 16) csz kz (Hv2' ms1 mat1 S' W' regsR memR mdR POST l off El) LY IMG Hsp (fun z m => AFix.DPOST3 W' ly regs0 ch B S' z m) Hkz1 Nrange B S' l off (HARm' ms1 mat1 S' W' regsR memR mdR POST) CI El Hcl_class eq_refl (Hoff_def' ms1 mat1 S' W' regsR memR mdR POST l off El) eq_refl)
as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| exact (TAILJ ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR CI POST l off El HA0 j0 jb j1 j2 j3 j4 Hj0 Hj1 Hj2 Hj3 Hj4 Hjb Hjb_def)].
intros [p s6] W6 c6 H [ns MP]. cbn [fst snd] in H, MP. apply (SHIFT ms1 mat1 Em HEm HSC MEQW S' W' regsR memR mdR RO POST (p, s6) W6 c6).
apply H. destruct MP as (WF' & _ & _ & _ & _ & QT). exact (conj WF' (QT (qmeter_tight _ HQT))).
Qed.
End e.
End d.
