(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YG0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG02 YG06 YG07 YG0m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8x.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3y YF3w YF3z YF41 YF3i YF0h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF54 YF40 YF5a YF5b YF5c YF59 YF5e YF58 YF56 YF55 YF57 YF42 YF07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1e YF8h YF8m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YA00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Lemma aview_eq_mbyte {imgk : img} : forall (H H' : word -> bool) (m m' : word -> option byte) a,
aview tfxsegs H' m' a = aview tfxsegs H m a -> mbyte tfxsegs (mrestrict H' m') a = mbyte tfxsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfxsegs (mrestrict H' m') a) as [b'|], (mbyte tfxsegs (mrestrict H m) a) as [b|]; cbn in E; try discriminate E; [|img_refl].
injection E as E. f_equal. img_apply bv_eq. img_exact E.
Qed.
Lemma val_mem_aview_xfer {imgk : img} : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfxsegs H' m' (a + Z.of_nat k) = aview tfxsegs H m (a + Z.of_nat k)) ->
val_mem tfxsegs (mrestrict H m) a n v -> val_mem tfxsegs (mrestrict H' m') a n v.
Proof. intros H H' m m' a n v HA Hv. eapply val_mem_ext; [|img_try (img_exact Hv)]. intros k Hk. img_apply aview_eq_mbyte. img_exact (HA k Hk). Qed.
Lemma apresent_aview_some {imgk : img} : forall (H : word -> bool) m a, TFX_IMG_END <= a < 2 ^ 64 -> apresent H m a -> aview tfxsegs H m a <> None.
Proof.
intros H m a Ha Hp. destruct (apresent_mbyte H m a Hp) as [b Hb]. unfold aview. rewrite Hb. cbn. discriminate.
Qed.
Lemma aview_some_apresent {imgk : img} : forall (H : word -> bool) m a, TFX_IMG_END <= a < 2 ^ 64 -> aview tfxsegs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hv. destruct (mbyte tfxsegs (mrestrict H m) a) as [b|] eqn:E.
- img_exact (mbyte_high_apresent H m a b Ha E).
- exfalso. img_apply Hv. unfold aview. rewrite E. img_refl.
Qed.
Lemma apresent_xfer {imgk : img} : forall (H H' : word -> bool) m m' a, TFX_IMG_END <= a < 2 ^ 64 ->
aview tfxsegs H' m' a = aview tfxsegs H m a -> apresent H m a -> apresent H' m' a.
Proof.
intros H H' m m' a Ha E Hp. img_apply aview_some_apresent; [img_try (img_exact Ha)|]. rewrite E. img_exact (apresent_aview_some H m a Ha Hp).
Qed.
Lemma val_mem_aview {imgk : img} : forall (H : word -> bool) m a (w : nat) v k, val_mem tfxsegs (mrestrict H m) a w v -> (k < w)%nat ->
aview tfxsegs H m (a + Z.of_nat k) = Some (YG0h.le_byte v w k).
Proof.
intros H m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. img_change (YG0h.le_byte v w k) with (YP0g.le_byte v w k). f_equal.
img_apply unsigned_lit_small8. unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma subregion_refl : forall r, subregion r r.
Proof. intros r. unfold subregion. split; [img_refl|]. split; [img_lia|]. split; [img_lia|]. split; [img_try (right; img_lia)|]. intros c Hc; img_exact Hc. Qed.
Lemma region_kept_view {imgk : img} : forall (H H' : word -> bool) (E : env) (m m' : word -> option byte) n lo hi wlo whi cs spv,
bv_unsigned (ew E n) = spv ->
(forall a, spv + lo <= a < spv + hi -> aview tfxsegs H' m' a = aview tfxsegs H m a) ->
TFX_IMG_END <= spv + lo -> spv + hi <= 2 ^ 64 -> (forall a, spv + wlo <= a < spv + whi -> spv + lo <= a < spv + hi) ->
region_kept tfxsegs E (mrestrict H m) (mrestrict H' m') (YQ0b.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros H H' E m m' n lo hi wlo whi cs spv Hn HA Hlo Hhi Hw.
split; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite Hn; intros a Ha.
- img_apply aview_eq_mbyte. img_apply HA. img_exact Ha.
- intros Hwr. pose proof (Hw a Ha) as Ha'. img_apply apresent_writable; [img_lia|]. img_apply (apresent_xfer H H' m m' a); [img_lia | img_try (img_apply HA; img_lia) |].
img_apply writable_high_apresent; [img_lia | img_try (img_exact Hwr)].
Qed.
Lemma extent_disjoint_sub : forall E r0 r r', YQ0b.r_base r' = YQ0b.r_base r0 -> YQ0b.r_lo r0 <= YQ0b.r_lo r' -> YQ0b.r_hi r' <= YQ0b.r_hi r0 ->
YQ0b.r_lo r' <= YQ0b.r_hi r' -> extent_disjoint E r0 r -> extent_disjoint E r' r.
Proof. intros E r0 r r' Hb Hlo Hhi Hwf H. unfold extent_disjoint in *. rewrite Hb. img_lia. Qed.
Lemma aowned_regs_only : forall B ly S S' a, regs_only S S' -> aowned B ly S' a <-> aowned B ly S a.
Proof.
intros B ly S S' a (Rck & Rsecs & _ & _ & _ & _ & Rfs & _). unfold aowned, aclient_byte, sec_extents, frames. rewrite Rck, Rfs. tauto.
Qed.
Lemma aowned_tick : forall B ly S a, aowned B ly (set_nev (st_nev S + 1) S) a <-> aowned B ly S a.
Proof. intros B ly S a. unfold aowned, aclient_byte, sec_extents, frames. cbn. tauto. Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. img_apply same_io_with_vm_backing. Qed.
Lemma E0_nondummy {imgk : img} : forall ly regs0 n ch cl csz cnt v j0 jb j1 j2 j3 j4 cnt' v' j0' jb' j1' j2' j3' j4' k, (k < 64)%nat -> PND k = true ->
ew (YF54.E0 ly regs0 n ch cl cnt v csz j0 jb j1 j2 j3 j4) k = ew (YF54.E0 ly regs0 n ch cl cnt' v' csz j0' jb' j1' j2' j3' j4') k.
Proof.
intros until k. intros Hk HP.
do 64 (destruct k as [|k]; [img_try (first [img_refl | discriminate HP]) |]). img_lia.
Qed.
Section e. Context {imgk : img}.
Variable B : asyms.
Hypothesis TS : TfxSyms B.
Hypothesis U1 : tfx_unwind_spec.
Hypothesis D1 : tfx_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly (0x533a4 + D_2c4) regs0 ch.
Hypothesis PRE : acall_pre tfxsegs B ly S W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Htr : In tr (as_universe B).
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Hypothesis Hmiss : pc_chunks (cache S (chunk_class n)) = [].
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let S1 : astate := set_nev (st_nev S + 1) S.
Let cl : Z := chunk_class n.
Let csz : Z := class_size cl.
Let mat0 : list word := m_vm_materialized md0.
Let md0' : list word -> Model := fun mat => with_vm_backing (m_vm_lazy md0) mat md0.
Let E0m : env := YF54.E0 ly regs0 n ch cl 1 0 csz 0 0 0 0 0 0.
Let DPOSTm : Z -> (word -> option byte) -> Prop := fun z m => YF59.DPOST3 W ly regs0 ch B S1 z m.
Lemma HAR0 : AR tfxsegs B ly S W mem0 md0. Proof. img_exact (proj1 PRE). Qed.
Lemma HARm0 : ARm B ly S (aview tfxsegs (w_H W) mem0). Proof. img_exact (proj1 HAR0). Qed.
Lemma Hev : aregime S. Proof. img_exact (proj1 (proj2 PRE)). Qed.
Lemma HAR1 : AR tfxsegs B ly S1 W mem0 md0. Proof. img_exact (AR_tick B ly S W mem0 md0 HAR0 Hev). Qed.
Lemma HARm1 : ARm B ly S1 (aview tfxsegs (w_H W) mem0). Proof. img_exact (proj1 HAR1). Qed.
Lemma LY : layout_ok ly. Proof. img_exact (am_layout _ _ _ _ HARm0). Qed.
Lemma IMG : img_cover ly. Proof. img_exact (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR0))). Qed.
Lemma HTSD : ly_tsd ly = TFX_TSD. Proof. rewrite (am_tsd _ _ _ _ HARm0). img_exact (ts_tsd B TS). Qed.
Lemma Htp : getr regs0 4 = w64 TFX_TP.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp' & _). rewrite (ts_tp B TS) in Htp'. img_exact Htp'. Qed.
Lemma Hgp : getr regs0 3 = w64 (as_gp B). Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). img_exact H. Qed.
Lemma Hra : YK0s.ret_ok (getr regs0 1). Proof. destruct PRE as (_ & _ & H & _). img_exact H. Qed.
Lemma Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Proof. destruct PRE as (_ & _ & _ & Hal & Hlo & Hbot & Hhi & _). unfold spZ in *. repeat split; assumption. Qed.
Lemma Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & H & _). img_exact H. Qed.
Lemma HQT : qtight S. Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). img_exact H. Qed.
Lemma Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [H _] & _). img_exact H. Qed.
Lemma Hch : if sp0 + 16 <? ly_top ly
then if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\ fpchain (rdword (aview tfxsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch
else ch = [].
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ H] & _). unfold frame0_ok, spZ, s0Z in H. img_exact H. Qed.
Lemma Hcl_class : cl = chunk_class n. Proof. img_refl. Qed.
Lemma Hcl : 1 <= cl <= 31. Proof. img_exact (@YF5a.Hcl' ly regs0 mem0 n cl 0 DPOSTm Nrange [] 0 Hcl_class). Qed.
Lemma Hcl_def : cl = class_id (YF54.R8v n + YF54.RZ).
Proof. pose proof (@YF54.case0_sizes n Nrange) as (L & RS & R8 & NP & FP & NS & RQ). (subst cl; cbv beta). unfold chunk_class. rewrite NS, <- RS. img_refl. Qed.
Lemma FP : from_primary n = true. Proof. pose proof (@YF54.case0_sizes n Nrange) as (_ & _ & _ & _ & FP' & _). img_exact FP'. Qed.
Lemma Hmiss1 : pc_chunks (cache S1 cl) = []. Proof. img_exact Hmiss. Qed.
Lemma Hvd : 0 <= 0 /\ 16 * 0 + 2 ^ 16 <= 2 ^ 32. Proof. img_lia. Qed.
Lemma Hcntd : 1 <= 1 <= 16. Proof. img_lia. Qed.
Lemma Hjbd : 0 <= 0 <= 255. Proof. img_lia. Qed.
Lemma Hv2d : 0 mod 2 = 0. Proof. img_refl. Qed.
Lemma Usp : 0 <= sp0 < 2 ^ 64. Proof. unfold sp0. img_apply u64_range. Qed.
Lemma STK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. pose proof (lo_top ly LY) as (_ & _ & _ & H4 & _ & _ & H7). split; [img_try (img_exact H7) | img_try (img_exact H4)]. Qed.
Lemma WfP1 : WfP (as_universe B) 1 1 1 S1. Proof. img_exact (WfP_tick _ S (am_wf _ _ _ _ HARm0) Hev). Qed.
Lemma SEEDM : st_ok tfxsegs E0m MK0 (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Proof.
img_exact (@YF58.SEEDM_ok _ _ imgk W ly regs0 mem0 n ch cl 1 0 csz 0 0 0 0 0 0 Hcl Hvd Hcntd Hjbd Hv2d LY IMG Hn Htp Hsp DPOSTm Nrange Hcl_def B S1 TS HTSD HARm1 Hpres0 Hmiss1).
Qed.
Lemma MISS1 : SRr tfxsegs W (cfg_at tfxsegs (0x53104 + D_2c4) regs0 mem0 md0) (YF56.at_STM W ly regs0 mem0 md0 n ch cl 1 0 csz 0 0 0 0 0 0 MK_CALL).
Proof.
replace (cfg_at tfxsegs (0x53104 + D_2c4) regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (md0' mat0))
by (img_try (unfold cfg_at, md0', mat0; rewrite with_vm_backing_id; img_refl)).
img_exact (@YF56.miss1 _ _ imgk W ly regs0 mem0 md0 n ch cl 1 0 csz 0 0 0 0 0 0 Hcl Hvd Hcntd Hjbd Hv2d LY IMG Hn Hra4096 Hsp Hch DPOSTm Nrange Hcl_def mat0 U1 [] 0 SEEDM).
Qed.
Section f.
Variables (ms1 : machine_state) (mat1 : list word) (Em : env).
Hypothesis HEm : forall k, (k < aHAV)%nat -> ew Em k = ew E0m k.
Hypothesis HSC : st_ok tfxsegs Em MK_CALL (restrict (w_H W) ms1).
Hypothesis MEQW : forall x : word, ~ YF56.WINM ly regs0 (bv_unsigned x) -> (ms_mem ms1) x = mem0 x.
Hypothesis PRESW : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a.
Hypothesis BUFW : forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms1)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).
Lemma ms1_shape : ms1 = mkst (ms_regs ms1) (w64 (0x3670c + D_150)) (ms_mem ms1) (seg_rom tfxsegs).
Proof. img_exact (st_ok_restrict_mkst tfxsegs (w_H W) Em _ _ HSC eq_refl). Qed.
Lemma HSC' : st_ok tfxsegs Em MK_CALL (mkst (ms_regs ms1) (w64 (0x3670c + D_150)) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfxsegs)).
Proof. pose proof HSC as H. rewrite ms1_shape in H. img_exact H. Qed.
Lemma Em2 : ew Em 2 = getr regs0 2. Proof. rewrite (HEm 2%nat ltac:(img_try ((img_case; cbv); img_lia))). img_refl. Qed.
Lemma Em3 : ew Em 3 = getr regs0 3. Proof. rewrite (HEm 3%nat ltac:(img_try ((img_case; cbv); img_lia))). img_refl. Qed.

Lemma Em32 : ew Em 32 = w64 T. Proof. rewrite (HEm 32%nat ltac:(img_try ((img_case; cbv); img_lia))). img_refl. Qed.
Lemma Em39 : ew Em 39 = w64 cl. Proof. rewrite (HEm 39%nat ltac:(img_try ((img_case; cbv); img_lia))). img_refl. Qed.
Lemma Em40 : ew Em 40 = w64 (YF54.Pv ly cl). Proof. rewrite (HEm 40%nat ltac:(img_try ((img_case; cbv); img_lia))). img_refl. Qed.
Lemma T_range : zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL.
Proof. pose proof (@YF54.high_facts _ imgk ly regs0 mem0 n 0 Hvd LY IMG DPOSTm) as (F1 & F2 & _). split; assumption. Qed.
Lemma R_ra : getr (ms_regs ms1) 1 = w64 (0x3626c + D_150). Proof. rreg HSC (1%bv : bv 5) R. img_exact R. Qed.
Lemma R_sp : getr (ms_regs ms1) 2 = w64 (sp0 - 2320).
Proof. rreg HSC (2%bv : bv 5) R. rewrite R, Em2. unfold w64, sp0. f_equal; img_lia. Qed.
Lemma R_gp : getr (ms_regs ms1) 3 = getr regs0 3. Proof. rreg HSC (3%bv : bv 5) R. rewrite R, Em3. img_refl. Qed.
Lemma R_tp : getr (ms_regs ms1) 4 = w64 TFX_TP. Proof. rreg HSC (4%bv : bv 5) R. img_exact R. Qed.
Lemma R_a0 : getr (ms_regs ms1) 10 = w64 (T + t_cache).
Proof. rreg HSC (10%bv : bv 5) R. rewrite R, Em32. unfold w64, t_cache. rewrite Zbv_add_unsigned. img_refl. Qed.
Lemma R_a1 : getr (ms_regs ms1) 11 = w64 (T + t_cache + 80 * cl). Proof. rreg HSC (11%bv : bv 5) R. rewrite R, Em40. img_refl. Qed.
Lemma R_a2 : getr (ms_regs ms1) 12 = w64 A_ALLOCATOR. Proof. rreg HSC (12%bv : bv 5) R. img_exact R. Qed.
Lemma R_a3 : getr (ms_regs ms1) 13 = w64 cl. Proof. rreg HSC (13%bv : bv 5) R. rewrite R, Em39. img_refl. Qed.
Lemma SP1 : spZ (ms_regs ms1) = sp0 - 2320.
Proof. unfold spZ. rewrite R_sp. unfold w64. img_apply unsigned_lit_small. pose proof Usp. pose proof Hsp. pose proof STK. unfold ASTACK, kHighMemBeg in *. img_lia. Qed.
Lemma UNW1 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms1)) (T + t_unwinding) 1 0.
Proof.
pose proof T_range as [T1 T2].
memv HSC 41%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite Em32; unfold w64, t_unwinding; rewrite unsigned_lit_small by (ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; img_lia); img_refl)
| img_refl | img_try (cbn; img_lia)].
Qed.

Lemma UNW_cell : forall Sx rd, ARm B ly Sx rd -> rd (T + t_unwinding) = Some 0.
Proof.
intros Sx rd M. assert (IN : In (z1 (AT t_unwinding) 0) (acells B ly Sx)).
{ unfold acells. repeat (img_apply in_app_iff; right). left. img_refl. }
pose proof (proj1 (Forall_forall _ _) (am_cells _ _ _ _ M) _ IN 0%nat ltac:(img_try (cbn; img_lia))) as X. cbn [c_at c_w aeval z1 c1] in X.
rewrite Z.add_0_r in X. img_exact X.
Qed.
Lemma AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> aview tfxsegs (w_H W) (ms_mem ms1) a = aview tfxsegs (w_H W) mem0 a.
Proof.
intros a Ha Hs. destruct (Z.eq_dec a (T + t_unwinding)) as [->|Hne].
- rewrite (UNW_cell S1 _ HARm1). pose proof (val_mem_aview (w_H W) (ms_mem ms1) (T + t_unwinding) 1 0 0 UNW1 ltac:(img_lia)) as X.
rewrite Z.add_0_r in X. rewrite X. img_refl.
- img_apply aview_same. img_apply MEQW. rewrite unsigned_lit_small by img_exact Ha. unfold YF56.WINM. fold sp0. unfold T in Hne. clear - Hs Hne. img_lia.
Qed.
Lemma AR1 : AR tfxsegs B ly S1 W (ms_mem ms1) (md0' mat1).
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof T_range as [T1 T2].
img_apply (AR_frame_law_ok tfxsegs B ly S1 W mem0 md0 (ms_mem ms1) (md0' mat1) HAR1).
- intros a Ha Ho. img_apply AG1; [img_try (img_exact Ha)|]. intros Hst. img_apply (AR_stack_law_ok tfxsegs B ly S1 W mem0 md0 a HAR1); [|img_try (img_exact Ho)].
clear - Hst Hlo Hhi. unfold ASTACK in *. img_lia.
- intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
assert (AV : forall m, aview tfxsegs (w_H W) m a = aview tfxsegs (w_H W) m a') by (img_try (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; img_refl)).
rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (img_try ((subst a'; cbv beta); img_apply u64_range)).
destruct (Z_lt_le_dec a' (sp0 - ASTACK)) as [H1|H1]; [|img_try (destruct (Z_lt_le_dec a' sp0) as [H2|H2])].
2:{ img_apply apresent_aview_some; [img_try (clear - H1 H2 K1 Ha' Hlo; unfold TFX_IMG_END, kHighMemBeg, ASTACK in *; img_lia) | img_try (img_apply PRESW; img_lia)]. }
all: rewrite (AG1 a' Ha' ltac:(img_lia)); img_exact Hv.
- img_apply m_vmmaps_wvb.
- img_apply m_vm_lazy_wvb.
- img_apply eager_used_wvb.
- intros a Ha Hx. rewrite (MEQW (w64 a)); [img_refl|].
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)).
unfold w64. rewrite unsigned_lit_small by img_exact Ha'. unfold YF56.WINM. fold sp0.
pose proof (zone3_apart_hsh _ _ a T1) as TH. unfold T in TH. clear - Ha K1 Hlo TH.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, kThreadObjSize in *. img_lia.
Qed.
Lemma REFILL_PRE : refill_pre B ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof HAR0 as (_ & _ & [BUD _] & _).
unfold refill_pre. rewrite SP1. unfold raZ. rewrite R_ra, R_gp, R_tp, R_a0, R_a1, R_a2, R_a3, Hgp, (ts_tp B TS).
split; [img_try (img_exact AR1)|].
split; [img_try (unfold abudget in *; cbn [st_nev set_nev S1]; img_change (sec_live_bytes S1) with (sec_live_bytes S); img_change (sec_hulls S1) with (sec_hulls S)  ; unfold EV_A in *; img_lia)|].
split; [split; [pose proof (wf_prim_ev _ _ _ _ _ WfP1) as PE; cbn [st_nev set_nev S1] in PE |- *; img_change (prim_user_mapped S1) with (prim_user_mapped S) in *; img_lia|];
split; [img_try (img_exact (aregime_preg_tick S cl Hev Hcl)) | img_try (img_exact (aregime_mid_tick S Hev))]|].
split; [img_try (img_apply qtight_qloose; img_exact HQT)|].
split; [img_try (img_apply ret_ok_even; img_refl)|]. split; [img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)|].
split; [img_try (clear - Hal; replace (sp0 - 2320) with (sp0 + (-145) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal)|].
split; [img_try (clear - Hlo; unfold ASTACK, RSTACK in *; img_lia)|]. split; [img_lia|].
split; [img_try (intros a Ha; img_apply PRESW; clear - Ha; unfold ASTACK, RSTACK in *; img_lia)|].
split; [img_refl|]. split; [img_refl|]. split; [img_refl|]. split; [img_refl|].
split; [img_refl|]. split; [img_refl|]. split; [img_try (img_exact Hcl) | img_try (img_exact Hmiss1)].
Qed.
Section g.
Variables (S' : astate) (W' : world tfxsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis WFP' : WfP (as_universe B) 0 1 1 S'.
Hypothesis RO : regs_only S1 S'.
Hypothesis CI : st_cache_inited S' = true.
Hypothesis POST : acall_post tfxsegs B RSTACK ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR.
Let msR : machine_state := mkst regsR (w64 (0x3626c + D_150)) memR (seg_rom tfxsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Lemma HAR' : AR tfxsegs B ly S' W' memR mdR. Proof. img_exact (proj1 POST). Qed.
Lemma HARm' : ARm B ly S' (aview tfxsegs (w_H W') memR). Proof. img_exact (proj1 HAR'). Qed.
Lemma WLE : wle W W'. Proof. img_exact (proj1 (proj2 (proj2 POST))). Qed.
Lemma ERRNO_low : as_errno B + 4 <= kHighMemBeg.
Proof. rewrite (ts_errno B TS). unfold TFX_ERRNO, kHighMemBeg. img_lia. Qed.
Lemma AGR : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2320 - RSTACK <= a < sp0 - 2320) ->
aview tfxsegs (w_H W') memR a = aview tfxsegs (w_H W) (ms_mem ms1) a.
Proof.
intros a Ha Hns. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof ERRNO_low as EL.
destruct POST as (_ & _ & _ & _ & _ & FR & _). img_apply FR.
- clear - Ha Hlo K1 U. unfold ASTACK, kHighMemBeg in *. img_lia.
- img_apply (AR_stack_law_ok tfxsegs B ly S1 W (ms_mem ms1) (md0' mat1) a AR1). clear - Ha Hlo Hhi. unfold ASTACK in *. img_lia.
- img_apply (AR_stack_law_ok tfxsegs B ly S' W' memR mdR a HAR'). clear - Ha Hlo Hhi. unfold ASTACK in *. img_lia.
- unfold ascratch. rewrite SP1. intros [X|X]; [img_try (img_exact (Hns X))|]. clear - X Ha Hlo K1 EL. unfold ASTACK, kHighMemBeg in *. img_lia.
- intros [].
Qed.
Lemma PRES' : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W') memR a.
Proof.
intros a Ha. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
assert (Hhi' : TFX_IMG_END <= a < 2 ^ 64) by (img_try (clear - Ha Hlo K1 U; unfold TFX_IMG_END, ASTACK, kHighMemBeg in *; img_lia)).
destruct (Z_lt_le_dec a (sp0 - 2320 - RSTACK)) as [H1|H1]; [|img_try (destruct (Z_lt_le_dec a (sp0 - 2320)) as [H2|H2])].
- img_apply (apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [img_try (img_apply AGR; [img_exact Ha | img_lia]) | img_try (img_apply PRESW; img_exact Ha)].
- destruct POST as (_ & _ & _ & _ & _ & _ & PRS). img_apply PRS. rewrite SP1. img_lia.
- img_apply (apresent_xfer (w_H W) (w_H W') (ms_mem ms1) memR a Hhi'); [img_try (img_apply AGR; [img_exact Ha | img_lia]) | img_try (img_apply PRESW; img_exact Ha)].
Qed.
Lemma BUF' : forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W') memR) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0).
Proof.
intros i Hi. pose proof (@YF54.tr_length imgk ly regs0 mem0 n ch 0 DPOSTm) as LEN. img_change (YF54.tr ly regs0 ch) with tr in LEN.
eapply val_mem_aview_xfer; [|img_try (img_exact (BUFW i Hi))]. intros k Hk. img_apply AGR; clear - Hi Hk LEN; unfold IFRAME, ASTACK, RSTACK in *; img_lia.
Qed.
Let E1 : env := havoc Em hRFk (map (getr regsR) CLOB).
Lemma Em2u : bv_unsigned (ew Em 2) = sp0. Proof. rewrite Em2. img_refl. Qed.
Lemma KEPT3 : Forall (region_kept tfxsegs Em (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W') memR)) RSK3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
assert (A : forall a, sp0 - 2320 <= a < sp0 -> aview tfxsegs (w_H W') memR a = aview tfxsegs (w_H W) (ms_mem ms1) a)
by (img_try (intros a Ha; img_apply AGR; clear - Ha; unfold ASTACK, RSTACK; img_lia)).
unfold RSK3. repeat (img_apply Forall_cons; [img_try (eapply (region_kept_view (w_H W) (w_H W') Em (ms_mem ms1) memR 2 _ _ _ _ _ sp0 Em2u);
[intros a Ha; img_apply A; clear - Ha; img_lia | clear - Hlo K1; unfold TFX_IMG_END, ASTACK, kHighMemBeg in *; img_lia | clear - U; img_lia | clear; intros a Ha; img_lia]) |]).
img_apply Forall_nil.
Qed.
Let ms3 : machine_state := mkst regsR (w64 (0x3626c + D_150)) (mrestrict (w_H W') memR) (seg_rom tfxsegs).
Lemma HS3 : st_ok tfxsegs E1 SSK3 ms3.
Proof.
rewrite SSK3_eq. pose proof MK_CALL_facts as (F1 & F2 & F3 & F4 & F5 & F6). destruct MK_CALL_mem3 as [rest ER].
apply (st_ok_after_call tfxsegs hRFk Em MK_CALL (mkst (ms_regs ms1) (w64 (0x3670c + D_150)) (mrestrict (w_H W) (ms_mem ms1)) (seg_rom tfxsegs))
regsR (mrestrict (w_H W') memR) RSK3 (0x3626c + D_150) HSC' F6 F1 F2 F3 F4).
- rewrite ER. img_change RSK3 with [K3bst; trim_lo K3scr (-2320); K3top].
img_apply submem_keep; [img_try (img_apply subregion_refl)|]. img_apply submem_keep; [img_try (img_apply subregion_trim_lo)|]. img_apply submem_keep; [img_try (img_apply subregion_refl)|]. img_apply submem_nil.
- img_exact F5.
- destruct POST as (_ & _ & _ & CS & _). intros r Hr. img_apply CS. img_exact Hr.
- img_exact KEPT3.
Qed.
Variables (l : list Z) (off : Z).
Hypothesis Hcache' : pc_chunks (cache S' cl) = l ++ [off].
Hypothesis HA0 : getr regsR 10 = w64 1.
Let cnt' : Z := Z.of_nat (length (l ++ [off])).
Let v' : Z := off / 16.
Let DPOST' : Z -> (word -> option byte) -> Prop := fun z m => YF59.DPOST3 W' ly regs0 ch B S' z m.
Lemma Hcnt_def' : cnt' = Z.of_nat (length (l ++ [off])). Proof. img_refl. Qed.
Lemma Hcsz_def : csz = class_size cl. Proof. img_refl. Qed.
Lemma Hoffv' : off = 16 * v' /\ v' mod 2 = 0.
Proof.
pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm') cl Hcl) as CL. pose proof (wr_elems _ _ _ _ _ _ CL) as EL. rewrite Hcache' in EL.
pose proof (proj1 (Forall_forall _ _) EL off ltac:(img_try (rewrite !in_app_iff; cbn; tauto))) as [_ O2].
pose proof (class_ok cl Hcl) as (K1 & K2 & _). apply Z.mod_divide in O2 as [q Hq]; [|img_lia]. apply Z.mod_divide in K2 as [r Hr]; [|img_lia].
(subst v'; cbv beta). rewrite Hq, Hr. replace (q * (r * 32)) with ((2 * q * r) * 16) by img_lia. rewrite Z.div_mul by img_lia. split; [img_lia|].
rewrite <- Z.mul_assoc, Z.mul_comm. img_apply Z_mod_mult.
Qed.
Lemma Hoff_def' : off = 16 * v'. Proof. img_exact (proj1 Hoffv'). Qed.
Lemma Hv2' : v' mod 2 = 0. Proof. img_exact (proj2 Hoffv'). Qed.
Lemma Hv' : 0 <= v' /\ 16 * v' + 2 ^ 16 <= 2 ^ 32.
Proof. img_exact (@YF5a.Hv' _ imgk W' ly regs0 memR n cl cnt' v' Hv2' DPOST' Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def'). Qed.
Lemma Hcnt' : 1 <= cnt' <= 16.
Proof. img_exact (@YF5a.Hcnt' _ imgk W' ly regs0 memR n cl cnt' v' Hv2' Hsp DPOST' Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def'). Qed.
Variables (j0 jb j1 j2 j3 j4 : Z).
Let Kv' : Z := YF54.Kv ly cl v'.
Let RZ : Z := YF54.RZ.
Hypothesis Hj0 : val_mem tfxsegs (mrestrict (w_H W') memR) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfxsegs (mrestrict (w_H W') memR) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfxsegs (mrestrict (w_H W') memR) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfxsegs (mrestrict (w_H W') memR) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfxsegs (mrestrict (w_H W') memR) (YF54.SSLOTv ly cl) 8 j4.
Hypothesis Hjb : 0 <= jb <= 255.
Hypothesis Hjb_def : val_mem tfxsegs (mrestrict (w_H W') memR) (Kv' + RZ - 15) 1 jb.
Let E0' : env := YF54.E0 ly regs0 n ch cl cnt' v' csz j0 jb j1 j2 j3 j4.
Let Es : env := env_merge PND E1 E0'.
Lemma HEs : forall k, (k < aHAV)%nat -> ew Es k = ew E0' k.
Proof.
intros k Hk. unfold aHAV in Hk. destruct (PND k) eqn:HP.
- unfold Es. rewrite (ew_merge_in PND E1 E0' k HP). unfold E1. rewrite ew_havoc_old by (img_try (unfold hRFk; img_lia)).
rewrite (HEm k Hk). unfold E0m, E0'. img_apply E0_nondummy; [img_try (img_exact Hk) | img_try (img_exact HP)].
- unfold Es. img_apply ew_merge_out. img_exact HP.
Qed.
Lemma AGs : env_agree 64 E0' Es.
Proof. split; [img_try (img_exact HEs) | img_refl]. Qed.
Lemma Es2 : bv_unsigned (ew Es 2) = sp0. Proof. rewrite (HEs 2%nat ltac:(img_try ((img_case; cbv); img_lia))). img_refl. Qed.
Lemma FACTS' : atoms_ok E0' (f_atoms FK).
Proof.
img_exact (@YF5c.FACTS_ok _ imgk W' ly regs0 memR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hn Hsp DPOST' Nrange Hcl_def B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def).
Qed.
Lemma REG0' : Forall (region_ok tfxsegs E0' (mrestrict (w_H W') memR)) REG0K.
Proof.
img_exact (@YF5b.REG0_ok _ imgk W' ly regs0 memR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hsp DPOST' Nrange B S' l off TS HTSD HARm' PRES' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Qed.
Lemma PAIRS' : pairwise_disjoint E0' REG0K.
Proof.
img_exact (@YF5c.PAIRS_ok _ imgk W' ly regs0 memR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hv2' LY IMG Hsp DPOST' Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def).
Qed.
Lemma HS4 : st_ok tfxsegs Es SSK3 ms3.
Proof.
pose proof SSK3_atoms as (A1 & A2 & A3 & A4 & A5). pose proof tlREG0K_facts as (_ & _ & T3).
img_apply (st_ok_agree_on2 tfxsegs PND E1 Es SSK3 ms3 HS3 (env_merge_on PND E1 E0') A1 A2 A3 A4).
rewrite A5. img_exact (atoms_ok_agree 64 E0' Es _ AGs T3 FACTS').
Qed.
Lemma HS5 : st_ok tfxsegs Es (mkSS (ss_pc SSK3) (sr_set (ss_regs SSK3) 10%bv (SLit 1)) (ss_mem SSK3) (ss_resv SSK3) (ss_facts SSK3)) ms3.
Proof.
img_apply (st_ok_pin_regU Es SSK3 ms3 10%bv (SLit 1) HS4); [img_try (intros X; discriminate X)|].
pose proof (st_ok_reg tfxsegs Es SSK3 ms3 10%bv HS4) as R. unfold U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. img_refl.
Qed.
Lemma region_ok_agree_on_lt : forall r, In r (tl REG0K) -> region_ok tfxsegs E0' (mrestrict (w_H W') memR) r -> region_ok tfxsegs Es (ms_mem ms3) r.
Proof.
intros r Hr H. pose proof tlREG0K_facts as (T1 & _). unfold ms3. cbn [ms_mem mkst].
img_apply (region_ok_agree tfxsegs 64 E0' Es _ r AGs); [|img_try (img_exact H)]. img_exact (proj1 (forallb_forall _ _) T1 r Hr).
Qed.
Lemma HS6 : st_ok tfxsegs Es (mkSS (0x3626c + D_150) (sr_set (ss_regs SSK3) 10%bv (SLit 1)) [K3bst; K3scr; K3top] None (ss_facts SSK3)) ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U.
pose proof (st_ok_mem_surgery Es _ ms3 [K3bst; K3scr; K3top] HS5) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. img_apply X. clear X.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val Es (Some 2%nat) = sp0) by (img_try (cbn [base_val]; img_exact Es2)).
split; [img_refl|]. split.
- img_apply Forall_cons; [img_try (img_exact (Forall_inv HF))|]. img_apply Forall_cons; [|img_try (img_exact (Forall_inv_tail (Forall_inv_tail HF)))].
pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, K3scr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite BV.
split; [img_try (clear - Hlo K1; unfold ASTACK, kHighMemBeg in *; img_lia)|]. split; [img_try (clear - U; img_lia)|]. split; [|img_try (img_exact R4)].
intros o Ho. img_apply apresent_writable; [img_try (clear - Ho Hlo K1 U; unfold TFX_IMG_END, ASTACK, kHighMemBeg in *; img_lia)|]. img_apply PRES'. clear - Ho; unfold ASTACK; img_lia.
- unfold K3bst, K3scr, K3top. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite BV. repeat split; img_lia.
Qed.
Lemma HS7 : st_ok tfxsegs Es MK_AFTER ms3.
Proof.
rewrite MK_AFTER_eq3. pose proof tlREG0K_facts as (T1 & T2 & T3).
pose proof (st_ok_mem_surgery Es _ ms3 ([K3bst; K3scr; K3top] ++ tl REG0K) HS6) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. img_apply X. clear X.
intros HM. pose proof PAIRS' as PP. img_change REG0K with (hd R_bst REG0K :: tl REG0K) in PP. destruct PP as [A0 PT].
pose proof REG0' as RR. img_change REG0K with (hd R_bst REG0K :: tl REG0K) in RR. apply Forall_inv_tail in RR.
img_apply mem_ok_app; [img_try (img_exact HM) | img_try (img_exact T2) | | |].
- img_apply Forall_forall. intros r Hr. img_apply (region_ok_agree_on_lt r Hr). img_exact (proj1 (Forall_forall _ _) RR r Hr).
- img_exact (pairwise_disjoint_agree 64 E0' Es (tl REG0K) AGs T1 PT).
- intros r Hr. pose proof (all_disjoint_In E0' _ _ r A0 Hr) as D0.
assert (Hb : obase_lt 64 (YQ0b.r_base r) = true).
{ pose proof (proj1 (forallb_forall _ _) T1 r Hr) as Ha. unfold region_atoms_lt in Ha. apply andb_prop in Ha as [Ha _]. img_exact Ha. }
pose proof (extent_disjoint_agree 64 E0' Es (hd R_bst REG0K) r AGs eq_refl Hb D0) as D. clear D0.
cbn [all_disjoint]. repeat split; img_apply extent_disjoint_sym;
(eapply (extent_disjoint_sub Es (hd R_bst REG0K) r); [img_refl | img_try (cbn; unfold ASTACK; img_lia) | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (img_exact D)]).
Qed.
Lemma ATJ : YF54.at_ST W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 MK_AFTER W' cR.
Proof.
split; [img_refl|]. exists msR, (m_vm_materialized mdR), Es. split; [img_refl|]. split; [img_try (img_exact HEs)|].
split; [img_try (unfold msR; rewrite restrict_mkst_fx; img_exact HS7)|].
split; [img_try (intros x _; img_refl)|]. split; [img_try (img_exact PRES') | img_try (img_exact BUF')].
Qed.
Lemma HKpres' : forall a, Kv' <= a < Kv' + RZ + YF54.R8v n -> apresent (w_H W') memR a.
Proof. img_exact (@YF5a.KPRES _ imgk W' ly regs0 memR n cl cnt' v' csz Hv2' LY Hsp DPOST' Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def). Qed.
Lemma HSKpres' : forall a, YF54.SKv ly cl v' <= a < YF54.SKv ly cl v' + (RZ + YF54.R8v n) / 8 -> apresent (w_H W') memR a.
Proof. img_exact (@YF5a.SKPRES _ imgk W' ly regs0 memR n cl cnt' v' csz Hv2' LY IMG Hsp DPOST' Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def). Qed.
Lemma HPB250' : YF54.NPv n mod 8 <> 0 -> val_mem tfxsegs (mrestrict (w_H W') memR) (YF54.PBv ly n cl v') 1 250.
Proof. img_exact (@YF5a.PB250 _ imgk W' ly regs0 memR n cl cnt' v' csz Hv2' LY IMG Hsp DPOST' Nrange B S' l off HARm' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def). Qed.
Lemma SEED' : st_ok tfxsegs E0' SS0K (restrict (w_H W') (mkst regs0 (w64 (0x53104 + D_2c4)) memR (seg_rom tfxsegs))).
Proof.
img_exact (@YF5c.SEED_ok _ _ imgk W' ly regs0 memR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hn Htp Hsp DPOST' Nrange Hcl_def B S' l off TS HTSD HARm' PRES' CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def).
Qed.
Lemma TAILJ : amreal tfxsegs (malloc_join n tr cl S') W' (cfg_at tfxsegs (0x3626c + D_150) regsR memR mdR)
(fun r W'' c'' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfxsegs B ly S' W' regs0 memR mdR n r W'' c'').
Proof.
replace (cfg_at tfxsegs (0x3626c + D_150) regsR memR mdR) with cR by (img_try (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; img_refl)).
eapply amreal_SRr_pre.
{ img_exact (@YF55.segJ _ _ imgk W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hv2' LY IMG Hsp DPOST' Nrange l off W' cR ATJ). }
intros W2 c2 _ HJ. pose proof (proj1 HJ) as EW. (subst W2; cbv beta).
img_exact (@YF5e.tail_inner _ _ imgk W' ly regs0 memR mdR n ch cl cnt' v' csz j0 jb j1 j2 j3 j4 Hcl Hv' Hcnt' Hjb Hv2' LY IMG Hn Htp Hra Hsp DPOST' HKpres' HSKpres' HPB250' Nrange Hcl_def (m_vm_materialized mdR) SEED' B S' l off TS HTSD HARm' Hgp CI Hcache' Hcl_class Hcnt_def' Hoff_def' Hcsz_def Hj4 Hjb_def Htr HAR' D1 (fun z m H => H) (fun z m H => H) c2 HJ).
Qed.
End g.
Lemma rw_writable : forall (m : word -> option byte) a, (0xa1000 + D_1000) <= a < (0x5ff000 + D_1000) -> writable_at tfxsegs m a.
Proof. intros m a Ha. unfold writable_at. img_apply YF07.tfx_rw_window. rewrite unsigned_lit_small by img_lia. img_exact Ha. Qed.
Lemma aview_rw_some : forall (Hh : word -> bool) m a, (0xa1000 + D_1000) <= a < (0x5ff000 + D_1000) -> aview tfxsegs Hh m a <> None.
Proof.
intros Hh m a Ha. unfold aview, mbyte. destruct (mrestrict Hh m (Z_to_bv 64 a)); cbn; [img_try (discriminate)|].
pose proof (YF07.tfx_rw_rom a Ha) as X. destruct (seg_rom tfxsegs (Z_to_bv 64 a)); [img_try (cbn; discriminate) | img_try (exfalso; img_exact (X eq_refl))].
Qed.
Section h.
Variables (S' : astate) (W' : world tfxsegs) (regsR : bvmap 5 word) (memR : word -> option byte) (mdR : Model).
Hypothesis RO : regs_only S1 S'.
Hypothesis CI : st_cache_inited S' = true.
Hypothesis POST : acall_post tfxsegs B RSTACK ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR.
Hypothesis Hc0 : pc_chunks (cache S' cl) = [].
Hypothesis HA0 : getr regsR 10 = w64 0.
Let msR : machine_state := mkst regsR (w64 (0x3626c + D_150)) memR (seg_rom tfxsegs).
Let cR : config := mkCfg msR (with_vm_backing (m_vm_lazy mdR) (m_vm_materialized mdR) mdR).
Let ms3 : machine_state := mkst regsR (w64 (0x3626c + D_150)) (mrestrict (w_H W') memR) (seg_rom tfxsegs).
Let E1 : env := havoc Em hRFk (map (getr regsR) CLOB).
Lemma HE1 : forall k, (k < aHAV)%nat -> ew E1 k = ew E0m k.
Proof. intros k Hk. unfold E1. unfold aHAV in Hk. rewrite ew_havoc_old by (img_try (unfold hRFk; img_lia)). img_apply HEm. img_exact Hk. Qed.
Lemma E1_2 : bv_unsigned (ew E1 2) = sp0. Proof. rewrite (HE1 2%nat ltac:(img_try ((img_case; cbv); img_lia))). img_refl. Qed.
Lemma HSN : st_ok tfxsegs E1 MK_N0 ms3.
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as Us.
pose proof (HS3 S' W' regsR memR mdR POST) as H3. fold E1 in H3. img_change (mkst regsR (w64 (0x3626c + D_150)) (mrestrict (w_H W') memR) (seg_rom tfxsegs)) with ms3 in H3.
assert (H4 : st_ok tfxsegs E1 (mkSS (ss_pc SSK3) (sr_set (ss_regs SSK3) 10%bv (SLit 0)) (ss_mem SSK3) (ss_resv SSK3) (ss_facts SSK3)) ms3).
{ img_apply (st_ok_pin_regU E1 SSK3 ms3 10%bv (SLit 0) H3); [img_try (intros X; discriminate X)|].
pose proof (st_ok_reg tfxsegs E1 SSK3 ms3 10%bv H3) as R. unfold U. rewrite <- R. unfold ms3. cbn [ms_regs mkst]. rewrite HA0. img_refl. }
rewrite MK_N0_eq. pose proof (st_ok_mem_surgery E1 _ ms3 ([K3bst; K3scr; K3top] ++ NREGS) H4) as X. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in X. img_apply X. clear X H4 H3.
intros (HW & HF & HP). unfold ms3 in *. cbn [ms_mem mkst] in *.
assert (BV : base_val E1 (Some 2%nat) = sp0) by (img_try (cbn [base_val]; img_exact E1_2)).
pose proof (PRES' S' W' regsR memR mdR POST) as PR.
assert (OOM1 : val_mem tfxsegs (mrestrict (w_H W') memR) (TFX_OOM + 1) 1 1).
{ pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (HARm' S' W' regsR memR mdR POST)) (z1 (ANum (TFX_OOM + 1)) 1)) as C.
rewrite (ts_const B TS ly) in C. specialize (C ltac:(img_try (unfold Tfx_const; img_apply in_app_iff; right; img_apply in_app_iff; left; img_apply (nth_error_In _ 60); img_refl))).
img_exact (cell_holds_val_mem B ly (w_H W') memR (ANum (TFX_OOM + 1)) 1 (ANum 1) C). }
split; [img_refl|]. split.
- img_apply Forall_cons; [img_try (img_exact (Forall_inv HF))|]. img_apply Forall_cons.
{ pose proof (Forall_inv (Forall_inv_tail HF)) as (R1 & R2 & R3 & R4). cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in R1, R2, R3, R4.
rewrite BV in R1, R2, R3, R4.
unfold region_ok, K3scr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite BV.
split; [img_try (clear - Hlo K1; unfold ASTACK, kHighMemBeg in *; img_lia)|]. split; [img_try (clear - Us; img_lia)|]. split; [|img_try (img_exact R4)].
intros o Ho. img_apply apresent_writable; [img_try (clear - Ho Hlo K1 Us; unfold TFX_IMG_END, ASTACK, kHighMemBeg in *; img_lia)|]. img_apply PR. clear - Ho; unfold ASTACK; img_lia. }
img_apply Forall_cons; [img_try (img_exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HF))))|].
unfold NREGS. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
+ unfold region_ok, lit1. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_try (unfold TFX_OOM; img_lia)|]. split; [img_try (unfold TFX_OOM; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. eapply chunk_ok_val; [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) |]. rewrite Z.add_0_l. img_exact OOM1.
+ unfold region_ok, oomR. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_try (unfold TFX_OOM; img_lia)|]. split; [img_try (unfold TFX_OOM; img_lia)|]. split; [|img_try (img_apply Forall_nil)]. intros o Ho. rewrite Z.add_0_l. img_apply rw_writable. unfold TFX_OOM in *. img_lia.
+ unfold region_ok, errR. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_try (unfold TFX_ERRNO; img_lia)|]. split; [img_try (unfold TFX_ERRNO; img_lia)|]. split; [|img_try (img_apply Forall_nil)]. intros o Ho. rewrite Z.add_0_l. img_apply rw_writable. unfold TFX_ERRNO in *. img_lia.
- unfold K3bst, K3scr, K3top, NREGS, lit1, oomR, errR. cbn [pairwise_disjoint all_disjoint app]. unfold extent_disjoint.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. rewrite !BV. cbn [base_val]. clear - Hlo K1 Us. unfold TFX_OOM, TFX_ERRNO, ASTACK, kHighMemBeg in *. repeat split; img_lia.
Qed.
Lemma ATN : YF57.at_STN W' ly regs0 memR mdR n ch cl 1 0 csz 0 0 0 0 0 0 MK_N0 W' cR.
Proof.
split; [img_refl|]. exists msR, (m_vm_materialized mdR), E1. split; [img_refl|]. split; [img_try (img_exact HE1)|].
split; [img_try (unfold msR; rewrite restrict_mkst_fx; img_exact HSN)|]. split; [img_refl | img_try (img_exact (PRES' S' W' regsR memR mdR POST))].
Qed.
Lemma errno_not_owned : forall a, TFX_ERRNO <= a < TFX_ERRNO + 4 -> ~ aowned B ly S' a.
Proof.
intros a Ha O. pose proof (HAR' S' W' regsR memR mdR POST) as AR'.
assert (IMGa : in_img tfxsegs a).
{ unfold in_img. rewrite YF07.tfx_segs_eq.
eexists. split; [img_try (do 3 right; left; img_refl)|]. img_case; cbn; unfold TFX_ERRNO in Ha; img_lia. }
apply (proj1 (AR_owned_image_law_ok tfxsegs B ly S' W' memR mdR a AR' IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfx_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]).
cbn [In] in Hr. unfold TFX_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [img_try (cbn [fst snd] in X1, X2; img_lia)|] | False => destruct Hr end.
Qed.
Lemma oom_owned : aowned B ly S' TFX_OOM.
Proof.
img_apply (own_area B ly S' _ (as_oom_byte B, 1) TFX_OOM (HARm' S' W' regsR memR mdR POST)); [img_try (unfold asyms_areas; cbn; tauto)|].
cbn [fst snd]. rewrite (ts_oom B TS). img_lia.
Qed.
Lemma TAILN : amreal tfxsegs (malloc_join n tr cl S') W' (cfg_at tfxsegs (0x3626c + D_150) regsR memR mdR)
(fun r W'' c'' => Wf (as_universe B) (snd r) /\ qtight (snd r) -> malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n r W'' c'').
Proof.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as Us. pose proof ERRNO_low as EL.
unfold malloc_join. rewrite bind_assoc_eq. eapply amreal_pure; [img_try (img_exact (pop_miss S' cl Hc0))|]. eapply amreal_pure; [img_refl|].
unfold malloc_K. cbn [amreal].
replace (cfg_at tfxsegs (0x3626c + D_150) regsR memR mdR) with cR by (img_try (unfold cfg_at, cR, msR; rewrite with_vm_backing_id; img_refl)).
eapply SRr_mono.
{ img_exact (@YF57.segN _ _ imgk W' ly regs0 memR mdR n ch cl 1 0 csz 0 0 0 0 0 0 Hvd LY IMG Htp Hra Hsp DPOSTm [] 0 W' cR ATN). }
intros W6 c6 _ HR [WF' QT']. cbn [fst snd] in WF', QT' |- *.
destruct HR as (-> & regs' & mem' & mat & -> & A0 & CS' & MEQ' & PRS' & VOOM & VERR).
pose proof POST as (AR' & _ & WLE & CS & SIO & FR & _). pose proof (HARm' S' W' regsR memR mdR POST) as M'.
exists ly, regs', mem', (with_vm_backing (m_vm_lazy mdR) mat mdR).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
split; [|img_try (split; [rewrite A0; cbn [sptr_addr sptr_exp aeval]; img_refl | img_exact QT'])].
assert (NWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> a <> TFX_OOM -> ~ (TFX_ERRNO <= a < TFX_ERRNO + 4) -> mem' (Z_to_bv 64 a) = memR (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3. img_apply MEQ'. rewrite unsigned_lit_small by img_exact Ra. unfold YF57.WINN. fold sp0. clear - N1 N2 N3. unfold IFRAME, ASTACK in *. img_lia. }
split.
{
img_apply (AR_oom B ly S' W' memR mem' mdR (with_vm_backing (m_vm_lazy mdR) mat mdR) TS AR').
- intros a Ra Ho NX. img_apply aview_same. img_apply NWIN; [img_try (img_exact Ra) | | img_try (clear - NX; unfold XJ in NX; img_lia) |].
+ intros ST. img_exact (AR_stack_law_ok tfxsegs B ly S' W' memR mdR a AR' ltac:(img_try (clear - ST Hlo Hhi; unfold ASTACK in *; img_lia)) Ho).
+ intros ER. img_exact (errno_not_owned a ER Ho).
- intros a Hv. set (x := Z_to_bv 64 a). set (a' := bv_unsigned x).
assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
assert (AV : forall m, aview tfxsegs (w_H W') m a = aview tfxsegs (w_H W') m a') by (img_try (intros m; unfold aview, mbyte, mrestrict; rewrite Ex; img_refl)).
rewrite AV in Hv |- *. assert (Ha' : 0 <= a' < 2 ^ 64) by (img_try ((subst a'; cbv beta); img_apply u64_range)).
destruct (Z_le_gt_dec (sp0 - ASTACK) a') as [G1|G1]; [img_try (destruct (Z_lt_ge_dec a' sp0) as [G2|G2])|].
{ img_apply apresent_aview_some; [img_try (clear - G1 G2 K1 Ha' Hlo; unfold TFX_IMG_END, kHighMemBeg, ASTACK in *; img_lia) | img_try (img_apply PRS'; img_lia)]. }
all: destruct (Z.eq_dec a' TFX_OOM) as [->|NO]; [img_try (img_apply aview_rw_some; unfold TFX_OOM; img_lia)|].
all: destruct (Z_le_gt_dec TFX_ERRNO a') as [G3|G3]; [img_try (destruct (Z_lt_ge_dec a' (TFX_ERRNO + 4)) as [G4|G4]; [img_apply aview_rw_some; unfold TFX_ERRNO in *; img_lia|])|].
all: rewrite (aview_same (w_H W') memR mem' a' (NWIN a' Ha' ltac:(img_lia) NO ltac:(img_lia))); img_exact Hv.
- img_apply m_vmmaps_wvb.
- img_apply m_vm_lazy_wvb.
- img_apply eager_used_wvb.
- intros a Ha Hx. unfold YG0u.w64. img_apply NWIN.
+ clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. img_lia.
+ clear - Ha K1 Hlo. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. img_lia.
+ clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFX_OOM in *. img_lia.
+ clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFX_ERRNO in *. img_lia. }
split; [img_try (img_apply layout_le_refl)|].
split; [img_try (img_exact WLE)|].
split.
{
intros r Hr'. unfold acallee_saved in Hr'.
assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by img_lia.
clear - RR CS'. repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; (subst r; cbv beta); img_apply CS'; cbn [In];
repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]). }
split; [img_try (img_exact (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_wvb md0 mat1) SIO) (same_io_wvb mdR mat)))|].
split; [|img_try (img_exact PRS')].
intros a Ha NO NO' NS NE.
assert (NO1 : ~ aowned B ly S1 a) by (img_try (intros O; img_apply NO; img_exact (proj1 (aowned_tick B ly S a) O))).
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (img_try (intros X; img_apply NS; unfold ascratch, spZ; left; img_exact X)).
assert (NER : ~ (TFX_ERRNO <= a < TFX_ERRNO + 4)) by (img_try (intros X; img_apply NS; unfold ascratch; right; rewrite (ts_errno B TS); img_exact X)).
assert (NOO : a <> TFX_OOM) by (img_try (intros ->; img_exact (NO' oom_owned))).
rewrite (aview_same (w_H W') memR mem' a (NWIN a Ha NST NOO NER)). rewrite (FR a Ha NO1 NO').
- img_exact (AG1 a Ha NST).
- unfold ascratch in NS |- *. rewrite SP1. unfold spZ in NS. fold sp0 in NS. intros [X|X]; img_apply NS; [img_try (left; clear - X; unfold ASTACK, RSTACK in *; img_lia) | img_try (right; img_exact X)].
- intros [].
Qed.
End h.
Lemma SHIFT : forall S' W' regsR memR mdR, regs_only S1 S' ->
acall_post tfxsegs B RSTACK ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) (fun _ => False) ly S' W' regsR memR mdR ->
forall r W6 c6, malloc_leaf tfxsegs B ly S' W' regs0 memR mdR n r W6 c6 -> malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n r W6 c6.
Proof.
intros S' W' regsR memR mdR RO POST r W6 c6 (ly' & regs' & mem' & md' & -> & AP & RA0 & QT).
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof STK as [K1 K2]. pose proof Usp as U. pose proof ERRNO_low as EL.
destruct AP as (AR6 & LLE & WLE6 & CS6 & SIO6 & FR6 & PRS6). destruct POST as (AR' & _ & WLE & _ & SIO & FR & _).
exists ly', regs', mem', md'. split; [img_refl|]. split; [|img_try (split; [img_exact RA0 | img_exact QT])].
split; [img_try (img_exact AR6)|]. split.
{ destruct RO as (_ & Rsecs & _). rewrite Rsecs in LLE. img_exact LLE. }
split; [img_try (img_exact (wle_trans _ _ _ _ WLE WLE6))|]. split; [img_try (img_exact CS6)|].
split; [img_try (img_exact (same_io_trans _ _ _ (same_io_trans _ _ _ (same_io_wvb md0 mat1) SIO) SIO6))|]. split; [|img_try (img_exact PRS6)].
intros a Ha NO NO6 NS NE.
assert (NO1 : ~ aowned B ly S1 a) by (img_try (intros O; img_apply NO; img_exact (proj1 (aowned_tick B ly S a) O))).
assert (NO' : ~ aowned B ly S' a) by (img_try (intros O; img_apply NO1; img_exact (proj1 (aowned_regs_only B ly S1 S' a RO) O))).
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (img_try (intros X; img_apply NS; unfold ascratch, spZ; left; img_exact X)).
rewrite (FR6 a Ha NO' NO6 NS NE). rewrite (FR a Ha NO1 NO').
- img_exact (AG1 a Ha NST).
- unfold ascratch in NS |- *. rewrite SP1. unfold spZ in NS. fold sp0 in NS. intros [X|X]; img_apply NS; [img_try (left; clear - X; unfold ASTACK, RSTACK in *; img_lia) | img_try (right; img_exact X)].
- intros [].
Qed.
End f.
Theorem malloc_missk :
amreal tfxsegs (malloc n tr S) W (cfg_at tfxsegs (0x53104 + D_2c4) regs0 mem0 md0) (malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n).
Proof.
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ img_apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) (am_wf _ _ _ _ HARm0) Hev); [img_try (unfold MALLOC_MAX; img_lia) | img_try (img_exact Hlive) | img_try (img_exact Htr)]. }
rewrite (malloc_primary_eq n tr S FP). eapply amreal_pure; [img_refl|].
eapply amreal_pure; [img_try (unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; img_apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; img_lia); img_refl)|].
fold S1. img_change (chunk_class n) with cl.
eapply (YG0d.amreal_mbind tfxsegs (refill_tree cl) (fun _ : unit => malloc_join n tr cl) S1 W _
(fun r W' c' => exists ms1 mat1 Em,
((forall k, (k < aHAV)%nat -> ew Em k = ew E0m k) /\ st_ok tfxsegs Em MK_CALL (restrict (w_H W) ms1) /\
(forall x : word, ~ YF56.WINM ly regs0 (bv_unsigned x) -> ms_mem ms1 x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a) /\
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms1)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0))) /\
((WfP (as_universe B) (1 - 1) 1 1 (snd r) /\ regs_only S1 (snd r) /\ st_cache_inited (snd r) = true) /\
refill_leaf B ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl r W' c'))).
-
eapply amreal_SRr_pre; [img_try (img_exact MISS1)|]. intros W1 c1 _ HC.
destruct HC as (-> & ms1 & mat1 & Em & -> & HEm & HSC & MEQW & PRESW & BUFW).
pose proof (tfx_refill_ok B TS ly S1 W (ms_regs ms1) (ms_mem ms1) (md0' mat1) cl (REFILL_PRE ms1 mat1 Em HEm HSC MEQW PRESW)) as RR.
unfold cfg_at, A_Refill in RR. rewrite (ms1_shape ms1 Em HSC) at 1. change (md0' mat1) with (with_vm_backing (m_vm_lazy md0) mat1 md0) in RR at 1.
pose proof (refill_tree_apost (as_universe B) 1 1 1 S1 cl WfP1 Hcl ltac:(img_lia) (aregime_preg_tick S cl Hev Hcl)) as APOST.
eapply amreal_mono; [| img_try (img_exact (amreal_apost tfxsegs _ _ W _ _ APOST RR))].
intros r W' c' H. exists ms1, mat1, Em. split; [|img_try (img_exact H)]. repeat (split; [img_try (assumption)|]). img_exact BUFW.
-
intros [] S' W' c' (ms1 & mat1 & Em & (HEm & HSC & MEQW & PRESW & BUFW) & (WFP' & RO & CI) & HL). cbn [fst snd] in WFP', RO, CI, HL.
destruct HL as (regsR & memR & mdR & -> & POST & HA0). cbn [snd] in HA0.
unfold raZ. rewrite (R_ra ms1 Em HSC). unfold w64 at 1. rewrite unsigned_lit_small by img_lia.
destruct (pc_chunks (cache S' cl)) as [|x t] eqn:El.
+
eapply amreal_mono; [| img_try (img_exact (TAILN ms1 mat1 Em HEm HSC MEQW PRESW S' W' regsR memR mdR POST El HA0))].
intros [p s6] W6 c6 H [ns MP]. cbn [fst snd] in H, MP. img_apply H. destruct MP as (WF' & _ & _ & _ & _ & QT). img_exact (conj WF' (QT HQT)).
+ assert (LX : exists l off, x :: t = l ++ [off]) by (img_try (exists (List.removelast (x :: t)), (List.last (x :: t) 0); img_apply List.app_removelast_last; discriminate)).
destruct LX as (l & off & LX). rewrite LX in El.
destruct (@YF5a.junk_values _ imgk W' ly regs0 memR n cl (Z.of_nat (length (l ++ [off]))) (off / 16) csz (Hv2' ms1 mat1 S' W' regsR memR mdR POST l off El) LY IMG Hsp (fun z m => YF59.DPOST3 W' ly regs0 ch B S' z m) Nrange B S' l off (HARm' ms1 mat1 S' W' regsR memR mdR POST) CI El Hcl_class eq_refl (Hoff_def' ms1 mat1 S' W' regsR memR mdR POST l off El) eq_refl)
as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
eapply amreal_mono; [| img_try (img_exact (TAILJ ms1 mat1 Em HEm HSC MEQW PRESW BUFW S' W' regsR memR mdR CI POST l off El HA0 j0 jb j1 j2 j3 j4 Hj0 Hj1 Hj2 Hj3 Hj4 Hjb Hjb_def))].
intros [p s6] W6 c6 H [ns MP]. cbn [fst snd] in H, MP. img_apply (SHIFT ms1 mat1 Em HEm HSC MEQW S' W' regsR memR mdR RO POST (p, s6) W6 c6).
img_apply H. destruct MP as (WF' & _ & _ & _ & _ & QT). img_exact (conj WF' (QT HQT)).
Qed.
End e.
End d.
