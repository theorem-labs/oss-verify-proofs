(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF0w YF34 YF35 YF37 YF36 YF3c YF3a YF38.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac numconst := ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kBatchClass, t_qc, t_cache, DRSTACK, KSTACK, TFX_IMG_END, TFX_TP, A_ALLOCATOR, A_RChunk, A_CDealloc, A_DoRecycle, YF34.YFRAME, YF35.YFRAME, YF37.YFRAME, YF36.YFRAME in *.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma chunk_atom8 {imgk : img} : forall E m base a k0 x, ew E k0 = w64 x -> 0 <= x < 2 ^ 64 -> val_mem tfxsegs m (base + a) 8 x ->
YQ0b.chunk_ok tfxsegs E m base (YQ0b.mkChunk a (CVal 8 (SOff k0 0))).
Proof.
intros E m base a k0 x Hk Hx Hm. eapply chunk_ok_val; [| img_try (img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact Hx) | img_try (cbn; img_lia) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Lemma chunk_atom8d {imgk : img} : forall E m base a k0 d x, ew E k0 = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + d < 2 ^ 64 -> val_mem tfxsegs m (base + a) 8 (x + d) ->
YQ0b.chunk_ok tfxsegs E m base (YQ0b.mkChunk a (CVal 8 (SOff k0 d))).
Proof.
intros E m base a k0 d x Hk Hx Hxd Hm. eapply chunk_ok_val; [| img_try (img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact Hxd) | img_try (cbn; img_lia) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. img_refl.
Qed.
Lemma afact_intro : forall E k0 x lo hi al, ew E k0 = w64 x -> 0 <= x < 2 ^ 64 -> lo <= x <= hi -> x mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E k0 (mkAF lo hi al).
Proof. intros E k0 x lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. Qed.
Lemma val_mem_apresent {imgk : img} : forall (H : word -> bool) mem a (n : nat) v a', val_mem tfxsegs (mrestrict H mem) a n v ->
a <= a' < a + Z.of_nat n -> TFX_IMG_END <= a' < 2 ^ 64 -> apresent H mem a'.
Proof.
intros H mem a n v a' Hv Ha Hhi.
assert (E : exists b, mbyte tfxsegs (mrestrict H mem) a' = Some b).
{ exists (Z_to_bv 8 (YP0g.le_byte v n (Z.to_nat (a' - a)))). replace a' with (a + Z.of_nat (Z.to_nat (a' - a))) at 1 by img_lia. img_apply Hv. img_lia. }
destruct E as [b Hb]. img_exact (mbyte_high_apresent H mem a' b Hhi Hb).
Qed.
Section e. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfxsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : dr_pre B ly X0 P0 W0 regs0 mem0 md0.
Local Notation sp0 := (YF38.sp0 regs0).
Local Notation sp1 := (YF38.sp1 regs0).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation U := (as_universe B).
Local Notation hdra := (YF38.hdra B ly).
Local Notation zlen := (@YF38.zlen _).
Local Notation SY := (YF38.SY regs0).
Local Notation acc := (YF38.acc B ly X0 W0 regs0 mem0 md0).
Local Notation common_regs := (YF38.common_regs regs0).
Local Notation loop_regs := (YF38.loop_regs regs0).
Local Notation frame_cells := (YF38.frame_cells ly regs0).
Local Notation tmp_cells := (YF38.tmp_cells ly regs0).
Local Notation ost := (YF38.ost B ly X0 W0 regs0 mem0 md0).
Local Notation rcst := (YF38.rcst B ly X0 W0 regs0 mem0 md0).
Local Notation rst := (YF38.rst B ly X0 W0 regs0 mem0 md0).
Local Notation cdst := (YF38.cdst B ly X0 W0 regs0 mem0 md0).
Local Notation qst := (YF38.qst B ly X0 W0 regs0 mem0 md0).
Lemma IMG : img_cover ly.
Proof. img_exact (img_cover_of_ledger ly X0 md0 (proj1 (proj2 (proj1 PRE)))). Qed.
Lemma entry_facts :
ly_stk_lo ly + DRSTACK <= sp0 /\ sp0 + 32 <= ly_stk_hi ly /\ sp0 mod 16 = 0 /\
getr regs0 3 = w64 (as_gp B) /\ getr regs0 4 = w64 TFX_TP /\ YK0s.ret_ok (getr regs0 1) /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof.
pose proof PRE as (HAR & _ & _ & _ & _ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & _).
destruct HAR as (M & _). pose proof (lo_top ly (am_layout _ _ _ _ M)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
rewrite (ts_tp _ TB) in Htp. unfold spZ in *. splits; assumption.
Qed.
Lemma sp_facts : kHighMemBeg + DRSTACK <= sp0 /\ sp0 + 32 <= kHighMemEnd /\ 0 <= sp0 < 2 ^ 64 /\ 0 <= sp1 < 2 ^ 64 /\ sp1 = sp0 - 112 /\ sp0 mod 16 = 0 /\ sp1 mod 16 = 0.
Proof.
pose proof entry_facts as (E1 & E2 & E3 & _ & _ & _ & E7 & E8).
assert (U0 : 0 <= sp0 < 2 ^ 64) by (img_try (unfold YF38.sp0; img_apply u64_range)).
unfold YF38.sp1, YF34.YFRAME. numconst. splits; try img_lia.
all: replace (sp0 - 112) with (sp0 + (-7) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact E3.
Qed.
Lemma sp1_val : forall regs, loop_regs regs -> bv_unsigned (getr regs 2) = sp1.
Proof. intros regs (R2 & _). rewrite R2. unfold w64. img_apply unsigned_lit_small. pose proof sp_facts as (_ & _ & _ & U1 & _). img_exact U1. Qed.
Lemma item_facts : forall X rd k, ARm B ly X rd -> In k (st_chunks X) ->
hdra k = ck_base B ly k + ck_rz k - kChunkHeaderSize /\ 4096 <= hdra k /\ hdra k + 16 <= ASAN_CEIL /\ hdra k mod 16 = 0 /\ 0 <= hdra k < 2 ^ 64.
Proof.
intros X rd k M Hk. pose proof (chunk_facts B ly X rd k M Hk) as CF. unfold cfacts in CF. destruct CF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & CK).
assert (HP : match ck_beg k with PPrim _ | PSec _ _ => True | _ => False end) by (img_try (destruct (ck_beg k); first [img_exact I | destruct CK])).
pose proof (hdr_addr B ly k HP) as EH. unfold YF38.hdra. rewrite EH.
pose proof (req_size_bounds (ck_req k) ltac:(img_lia)) as (_ & Q1 & _). ceil; unfold in_app, zone3, TFX_IMG_LO, kLowShadowBeg, kChunkHeaderSize, kHighMemBeg, ASAN_CEIL in *.
splits; img_lia.
Qed.
Lemma slot_facts : forall X rd z, ARm B ly X rd -> slot_ok X z ->
kHighMemBeg <= SB + z /\ SB + z + kBatchBytes <= ASAN_CEIL /\ (SB + z) mod 8192 = 0 /\
ly_prim ly <= SB + z /\ SB + z + kBatchBytes <= ly_prim ly + kPrimResvSize /\
SB + region_off kBatchClass <= SB + z /\ SB + z + kBatchBytes <= SB + region_off kBatchClass + 2 ^ 31 /\ 0 <= SB + z < 2 ^ 64 /\
(forall a, bslot ly z a -> ~ (ly_stk_lo ly <= a < ly_stk_hi ly)).
Proof.
intros X rd z M SZ. pose proof (slot_carved B ly X rd z M SZ) as (C1 & C2 & C3). pose proof SZ as (Z1 & Z2 & Z3).
pose proof (slot_high B ly X rd z M SZ) as SH. pose proof (slot_not_stack B ly X rd z M SZ) as NS.
pose proof (lo_space_al ly (am_layout _ _ _ _ M)) as SAL.
assert (A0 : bslot ly z (SB + z)) by (img_try (unfold bslot, kBatchBytes; img_lia)).
assert (A1 : bslot ly z (SB + z + kBatchBytes - 1)) by (img_try (unfold bslot, kBatchBytes; img_lia)).
pose proof (SH _ A0) as ((P1 & _) & (H1 & _) & (G1 & _)). pose proof (SH _ A1) as ((_ & P2) & (_ & H2) & (_ & G2)).
rewrite class_size_24 in Z2. rewrite region_off_24 in *. unfold kBatchBytes in *.
unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, TFX_IMG_END in *. splits; try img_lia. img_exact NS.
Qed.
Lemma sb_cell : forall X (W : world tfxsegs) mem, ARm B ly X (aview tfxsegs (w_H W) mem) -> val_mem tfxsegs (mrestrict (w_H W) mem) (A_ALLOCATOR + 32) 8 SB.
Proof.
intros X W mem M. replace (A_ALLOCATOR + 32) with (aeval B ly (AInst o_space)) by (img_try (cbn; rewrite (ts_inst _ TB); img_refl)).
replace SB with (aeval B ly (ASp 0)) by (img_try (cbn; img_lia)). img_apply (tfx_const_lookup_sym B TB ly X (w_H W) mem _ 8 _ M). img_case; vm_compute. all: img_refl.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Lemma seed_O : forall X b t lz qb W regs mem md k0 ks, ost X (b :: t) lz qb W regs mem md -> b_items b = k0 :: ks ->
YF35.free_hyps W ly regs mem (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz.
Proof.
intros X b t lz qb W regs mem md k0 ks ST Hk0. destruct ST as [AC RX NE LEN CR LR A0 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. destruct HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7).
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27).
pose proof (lo_top ly (am_layout _ _ _ _ M)) as (_ & _ & _ & T4 & _ & _ & T7).
assert (SZb : slot_ok X (b_self b)) by (img_try (img_apply (RIx_slots U 0 0 0 X [] (b :: t) [] _ RX); cbn; left; img_refl)).
pose proof (slot_facts X _ (b_self b) M SZb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BNS).
pose proof (RIx_open U 0 0 0 X b t RX) as [RXo BL].
assert (Hk0in : In k0 (st_chunks X)).
{ destruct RXo as (_ & IT & _). rewrite Hk0 in IT. cbn [app] in IT. inversion IT as [|x l [H1 _] _]; (subst; cbv beta). img_exact H1. }
pose proof (item_facts X _ k0 M Hk0in) as (I0 & I1 & I2 & I3 & I4).
assert (NXf : 0 <= firstaddr ly t < ASAN_CEIL /\ firstaddr ly t mod 8192 = 0).
{ destruct t as [|b' t']; [img_try (cbn; ceil; unfold ASAN_CEIL; split; [img_lia | img_refl])|]. cbn [firstaddr].
assert (SZ' : slot_ok X (b_self b')) by (img_try (img_apply (RIx_slots U 0 0 0 X [] (b :: b' :: t') [] _ RX); cbn; right; left; img_refl)).
pose proof (slot_facts X _ (b_self b') M SZ') as (B1' & B2' & B3' & _). unfold zone3, TFX_IMG_LO, kLowShadowBeg, kBatchBytes, kHighMemBeg in *. img_lia. }
pose proof (batch_head_cells B ly (w_H W) mem b t CE) as (V0 & V8 & V16 & VI). cbv zeta in V0, V8, V16, VI.
pose proof (VI 0%nat k0 ltac:(img_try (rewrite Hk0; img_refl))) as V24. rewrite Z.mul_0_r, Z.add_0_r in V24. fold (hdra k0) in V24.
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FR as [CB SV].
assert (LENb : 1 <= zlen (b_items b) <= kBatchSlots) by (img_try (clear - BL; unfold YF38.zlen, kBatchSlots in *; img_lia)).
assert (LENr : 1 <= zlen (b :: t) < 2 ^ 40) by (img_try (clear - LEN; rewrite zlen_cons in *; unfold YF38.zlen in *; img_lia)).
constructor.
- img_exact (am_layout _ _ _ _ M).
- img_exact IMG.
- rewrite C4. img_exact Etp.
- rewrite SPV. unfold YF35.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by img_lia. split; [img_try (img_exact E1) | img_try (img_exact E2)].
- rewrite SPV. img_exact S7.
- rewrite SPV. intros a Ha. img_apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YF38.SY. unfold YF35.YFRAME in Ha. numconst. img_lia.
- rewrite SPV. unfold YF35.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by img_lia. splits; assumption.
- splits; [img_try (img_exact B4) | img_try (img_exact B5) | img_try (img_exact B3) |]. intros a Ha.
assert (HH : TFX_IMG_END <= a < 2 ^ 64) by (img_try (clear - Ha B1 B2; numconst; img_lia)).
destruct (Z_lt_le_dec a (SB + b_self b + 8)) as [L1|L1]; [img_try (img_apply (val_mem_apresent _ _ _ 8 _ a V0); [clear - Ha L1; cbn; img_lia | img_exact HH])|].
destruct (Z_lt_le_dec a (SB + b_self b + 16)) as [L2|L2]; [img_try (img_apply (val_mem_apresent _ _ _ 8 _ a V8); [clear - L1 L2; cbn; img_lia | img_exact HH])|].
destruct (Z_lt_le_dec a (SB + b_self b + 24)) as [L3|L3]; [img_try (img_apply (val_mem_apresent _ _ _ 8 _ a V16); [clear - L2 L3; cbn; img_lia | img_exact HH])|].
img_apply (val_mem_apresent _ _ _ 8 _ a V24); [img_try (clear - L3 Ha; cbn; img_lia) | img_try (img_exact HH)].
- img_exact NXf.
- img_exact LENb.
- split; [img_try (img_apply mod64_range) | img_try (img_exact Rqb)].
- img_exact LENr.
- img_exact Rlz.
- splits; [img_try (img_exact I1) | img_try (img_exact I2) | img_try (img_exact I3)].
-
rewrite restrict_mkst_fx. unfold YF35.SS0, YF35.SR0, sr_set. cbn [bv_eqb]. unfold YF35.E0, w64. img_apply (entry_st_ok_full tfxsegs).
+ img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_pin; [img_apply regs_ok_Ereg| intros XX; discriminate |]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|]|intros XX; discriminate|])|img_try (intros XX; discriminate)|].
* cbn [sv_denot]. rewrite C4, Etp. img_refl.
* cbn [sv_denot]. fold (YF35.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
rewrite (YF35.E2 ly regs), R2, R8. unfold YF35.YFRAME, w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
* cbn [sv_denot]. rewrite R9. img_refl.
* cbn [sv_denot]. rewrite R18. img_refl.
* cbn [sv_denot]. rewrite R19. img_refl.
* cbn [sv_denot]. rewrite R21. img_refl.
* cbn [sv_denot]. fold (YF35.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
rewrite (YF35.EqSZ ly regs), A0. unfold w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
+ img_case; vm_compute. all: img_refl.
+ cbn [ms_mem mkst]. fold (YF35.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
set (E0 := YF35.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
assert (BV2 : bv_unsigned (ew E0 2) = sp1) by (img_try ((subst E0; cbv beta); rewrite (YF35.E2 ly regs); img_exact SPV)).
assert (BV40 : bv_unsigned (ew E0 40) = SB + b_self b) by (img_try ((subst E0; cbv beta); rewrite (YF35.EqB ly regs); unfold w64; img_apply unsigned_lit_small; img_exact B8)).
unfold YF35.REG0, YF35.R_STK, YF35.R_B, YF35.YFRAME. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
* reg_intro. rewrite BV2. split; [img_lia|]. split; [img_try (numconst; img_lia)|]. split.
{ intros o Ho. img_apply apresent_writable; [img_try (numconst; img_lia)|]. img_apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YF38.SY. numconst. img_lia. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
-- img_apply (chunk_atom8 E0 _ _ _ 46%nat (zlen (b :: t))); [img_refl | img_lia | img_try (eapply val_mem_addr; [img_exact T0 | img_lia])].
-- img_apply (chunk_atom8 E0 _ _ _ 40%nat (SB + b_self b)); [img_refl | img_try (img_exact B8) | img_try (eapply val_mem_addr; [img_exact T8 | cbn [firstaddr]; img_lia])].
-- img_apply (chunk_atom8 E0 _ _ _ 49%nat lz); [img_refl | img_try (numconst; img_lia) | img_try (eapply val_mem_addr; [img_exact T16 | img_lia])].
-- img_apply (chunk_atom8 E0 _ _ _ 47%nat qb); [img_refl | img_lia | img_try (eapply val_mem_addr; [img_exact T24 | img_lia])].
* reg_intro. rewrite BV40. split; [img_lia|]. split; [img_try (numconst; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
repeat img_apply Forall_cons; try img_apply Forall_nil.
-- img_apply (chunk_atom8 E0 _ _ _ 41%nat (firstaddr ly t)); [img_refl | img_try (numconst; img_lia) | img_try (eapply val_mem_addr; [img_exact V0 | img_lia])].
-- img_apply (chunk_atom8 E0 _ _ _ 42%nat (b_bytes b mod 2 ^ 64)); [img_refl | img_try (img_apply mod64_range) | img_try (eapply val_mem_addr; [img_apply val_mem_mod64; img_exact V8 | img_lia])].
-- img_apply (chunk_atom8 E0 _ _ _ 43%nat (zlen (b_items b))); [img_refl | img_try (numconst; img_lia) | img_try (eapply val_mem_addr; [img_exact V16 | img_lia])].
-- img_apply (chunk_atom8 E0 _ _ _ 44%nat (hdra k0)); [img_refl | img_try (img_exact I4) | img_try (eapply val_mem_addr; [img_exact V24 | img_lia])].
+ img_apply pairwise_disjoint_of_extents. unfold YF35.REG0, YF35.R_STK, YF35.R_B, YF35.YFRAME, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
fold (YF35.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
rewrite (YF35.E2 ly regs), (YF35.EqB ly regs), SPV. unfold w64. rewrite unsigned_lit_small by img_exact B8.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (A0' : bslot ly (b_self b) (SB + b_self b)) by (img_try (unfold bslot, kBatchBytes; img_lia)). pose proof (BNS _ A0') as NS0.
split; [|img_try (img_exact (conj I I))]. split; [|img_try (img_exact I)]. clear - NS0 E1 E2 S5 B1 B2. numconst. img_lia.
+ split; [|img_try (split; img_exact I)]. cbn [YF35.FFO f_atoms atoms_ok].
fold (YF35.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
set (E0 := YF35.E0 ly regs (SB + b_self b) (firstaddr ly t) (b_bytes b mod 2 ^ 64) (zlen (b_items b)) (hdra k0) (zlen (b :: t)) qb lz).
assert (E2' : ew E0 2 = w64 sp1) by (img_try ((subst E0; cbv beta); rewrite (YF35.E2 ly regs); img_exact R2)).
pose proof (mod64_range (b_bytes b)) as MB. ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kBatchSlots, YF35.YFRAME.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kBatchBytes, kBatchSlots in S1, S2, B1, B2, NXf, LENb, I1, I2, Rlz.
split. { img_apply (afact_intro E0 2%nat sp1); [img_try (img_exact E2')| img_try (img_exact U1) | img_lia | img_try (img_change (2 ^ 4) with 16; img_exact S7) | img_lia]. }
split. { img_apply (afact_intro E0 40%nat (SB + b_self b)); [img_refl | img_try (img_exact B8) | img_lia | img_try (img_change (2 ^ 13) with 8192; img_exact B3) | img_lia]. }
split. { img_apply (afact_intro E0 41%nat (firstaddr ly t)); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 13) with 8192; img_exact (proj2 NXf)) | img_lia]. }
split. { img_apply (afact_intro E0 42%nat (b_bytes b mod 2 ^ 64)); [img_refl | img_try (img_exact MB) | img_lia | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (afact_intro E0 43%nat (zlen (b_items b))); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (afact_intro E0 44%nat (hdra k0)); [img_refl | img_try (img_exact I4) | img_lia | img_try (img_change (2 ^ 4) with 16; img_exact I3) | img_lia]. }
split. { img_apply (afact_intro E0 46%nat (zlen (b :: t))); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split. { img_apply (afact_intro E0 47%nat qb); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
split; [|img_try (img_exact I)]. { img_apply (afact_intro E0 49%nat lz); [img_refl | img_lia | img_lia | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
Qed.
Lemma T_SB_facts : forall X rd, ARm B ly X rd ->
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ T mod 4096 = 0 /\ kHighMemBeg <= SB /\ SB + kSpaceSize + 4096 <= ASAN_CEIL /\ SB mod 65536 = 0.
Proof.
intros X rd M. pose proof (am_layout _ _ _ _ M) as LO.
pose proof (lo_high ly LO) as HI. unfold in_high in HI. cbn [fst snd] in HI.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear; unfold kThreadObjSize; img_lia)) (Forall_nth_f _ _ 2 _ (lo_app ly LO) eq_refl) (pairwise_ij_f _ _ 2 6 _ _ (lo_disj ly LO) eq_refl eq_refl)) as ZT.
pose proof (lo_T_al ly LO) as TAL. pose proof (lo_space_al ly LO) as SAL. pose proof (lo_space_in ly LO) as [S1 S2]. unfold page_aligned in *. cbn [fst snd] in *.
split; [img_try (img_exact ZT)|]. split; [img_try (clear - ZT; unfold zone3 in ZT; img_lia)|]. clear ZT. splits; img_lia.
Qed.
Definition next_hdr (its : list chunk) : Z := match its with k :: _ => hdra k | [] => 0 end.
Lemma seed_R : forall X b t its i lz qb W regs mem md, rst X b t its i lz qb W regs mem md ->
YF37.free_hyps W ly regs mem (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i).
Proof.
intros X b t its i lz qb W regs mem md ST. destruct ST as [AC RX ITS Hi BL LEN CR LR BR S7 S9 FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. destruct HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7').
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27). pose proof BR as (R20 & R22 & R24).
pose proof (T_SB_facts X _ M) as (FT1 & FT2 & FT3 & FS1 & FS2 & FS3).
assert (SZb : slot_ok X (b_self b)) by (img_try (img_apply (RIx_slots U 0 0 0 X its t [b_self b] _ RX); cbn; left; img_refl)).
pose proof (slot_facts X _ (b_self b) M SZb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BNS).
destruct ITS as (done & Hits & Hdone).
assert (LENi : Z.of_nat i + zlen its = zlen (b_items b)) by (img_try (rewrite Hits, zlen_app; unfold YF38.zlen; rewrite Hdone; img_lia)).
assert (LENb : 1 <= zlen (b_items b) <= kBatchSlots) by (img_try (clear - BL; unfold YF38.zlen, kBatchSlots in *; img_lia)).
assert (Hi1 : 1 <= Z.of_nat i) by (img_try (clear - Hi; img_lia)).
assert (Hzi : 0 <= zlen its) by (img_try (unfold YF38.zlen; clear; img_lia)).
pose proof (batch_head_cells B ly (w_H W) mem b t CE) as (V0 & V8 & V16 & VI). cbv zeta in V0, V8, V16, VI.
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FR as [CB SV].
assert (NH : 0 <= next_hdr its < ASAN_CEIL /\ next_hdr its mod 16 = 0 /\ 0 <= next_hdr its < 2 ^ 64 /\
(Z.of_nat i < zlen (b_items b) -> exists k ks, its = k :: ks /\ In k (st_chunks X) /\ nth_error (b_items b) i = Some k)).
{ destruct its as [|k ks].
- cbn [next_hdr]. rewrite zlen_nil in LENi. ceil; unfold ASAN_CEIL. splits; try img_lia; try img_refl; (intros HH; exfalso; clear - HH LENi; img_lia).
- cbn [next_hdr]. destruct RX as (_ & IT & _). cbn [app] in IT. inversion IT as [|x l [Hk _] _]; (subst x l; cbv beta).
pose proof (item_facts X _ k M Hk) as (I0 & I1 & I2 & I3 & I4). splits; try assumption; [img_try (clear - I4; img_lia) | img_try (clear - I2; img_lia) | img_try (clear - I4; img_lia) | img_try (clear - I4; img_lia) |].
intros _. exists k, ks. splits; [img_refl | img_try (img_exact Hk) |]. rewrite Hits. rewrite nth_error_app2 by img_lia. rewrite Hdone, Nat.sub_diag. img_refl. }
destruct NH as (NH1 & NH2 & NH3 & NHk).
assert (S7R : kHighMemBeg <= YF37.S7v (SB + b_self b) (Z.of_nat i) /\ YF37.S7v (SB + b_self b) (Z.of_nat i) + 8 <= ASAN_CEIL /\
YF37.S7v (SB + b_self b) (Z.of_nat i) mod 8 = 0).
{ unfold YF37.S7v. rewrite region_off_24 in B6, B7. clear - B1 B3 B6 B7 LENi LENb Hzi FS2 Hi1. numconst. splits; img_lia. }
destruct S7R as (Q1 & Q2 & Q3).
constructor.
- img_exact (am_layout _ _ _ _ M).
- img_exact IMG.
- rewrite C4. img_exact Etp.
- rewrite SPV. unfold YF37.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by img_lia. split; [img_try (img_exact E1) | img_try (img_exact E2)].
- rewrite SPV. img_exact S7'.
- rewrite SPV. intros a Ha. img_apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YF38.SY. unfold YF37.YFRAME in Ha. clear - Ha S5; numconst. img_lia.
- rewrite SPV. unfold YF37.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by img_lia.
splits; try assumption; first [rewrite S7; unfold YF37.S7v; f_equal; img_lia | rewrite S9; f_equal; img_lia].
- rewrite SPV. eapply val_mem_addr; [img_try (img_exact CB) | img_refl].
- img_exact (sb_cell X W mem M).
- splits; [img_try (img_exact B6) | img_try (img_exact B7) | img_try (img_exact B3)].
- clear - LENi LENb Hi1 Hzi. img_lia.
- intros HLT. destruct (NHk HLT) as (k & ks & -> & Hk & Hnth). cbn [next_hdr]. pose proof (item_facts X _ k M Hk) as (I0 & I1 & I2 & I3 & I4).
pose proof (VI i k Hnth) as V. fold (hdra k) in V. splits; [img_try (eapply val_mem_addr; [img_exact V | img_lia]) | | img_try (img_exact I1) | img_try (img_exact I2) | img_try (img_exact I3)].
intros a Ha. img_apply (val_mem_apresent _ _ _ 8 _ a V); [img_try (clear - Ha; cbn; img_lia) | img_try (clear - Ha B1 B2 LENi LENb Hzi Hi1; numconst; img_lia)].
- split; [img_try (img_exact NH1) | img_try (img_exact NH2)].
-
rewrite restrict_mkst_fx. unfold YF37.SS0, YF37.SR0, sr_set. cbn [bv_eqb]. unfold YF37.E0, w64. img_apply (entry_st_ok_full tfxsegs).
+ set (E0 := Ereg regs (YF37.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))).
assert (HE2 : ew E0 2 = Z_to_bv 64 sp1) by (img_try (rewrite (YF37.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew E0 2 = getr regs 2); img_exact R2)).
repeat (img_apply regs_ok_pin; [| img_try (intros XX; discriminate) |]); [img_try (img_apply regs_ok_Ereg) | ..]; cbn [sv_denot].
* rewrite C4, Etp. img_refl.
* rewrite HE2, R8. unfold YF37.YFRAME, w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
* rewrite R9. img_refl.
* rewrite R18. img_refl.
* rewrite R19. img_refl.
* rewrite R21. img_refl.
* img_change (ew E0 40) with (Z_to_bv 64 (SB + b_self b)). rewrite R20. unfold w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
* img_change (ew E0 43) with (Z_to_bv 64 (zlen (b_items b))). rewrite R22. unfold w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
* img_change (ew E0 45) with (Z_to_bv 64 (YF37.S7v (SB + b_self b) (Z.of_nat i))). rewrite S7. unfold YF37.S7v, w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
* img_change (ew E0 43) with (Z_to_bv 64 (zlen (b_items b))). rewrite R24. unfold w64. rewrite Zbv_add_unsigned. img_refl.
* img_change (ew E0 52) with (Z_to_bv 64 (Z.of_nat i)). rewrite S9. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
+ img_case; vm_compute. all: img_refl.
+ cbn [ms_mem mkst]. set (E0 := Ereg regs (YF37.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))).
assert (BV2 : bv_unsigned (ew E0 2) = sp1) by (img_try (rewrite (YF37.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew E0 2 = getr regs 2); img_exact SPV)).
unfold YF37.REG0, YF37.R_STK, fatom8, YF37.YFRAME. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
* reg_intro. rewrite BV2. split; [img_lia|]. split; [img_try (clear - S2 S5; numconst; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom8d E0 _ _ _ 32%nat t_cache T); [img_refl | img_try (clear - FT1 FT2; numconst; img_lia) | img_try (clear - FT1 FT2; numconst; img_lia) | img_try (eapply val_mem_addr; [img_exact CB | img_refl])].
* reg_intro. split; [img_try (numconst; img_lia)|]. split; [img_try (numconst; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply (chunk_atom8 E0 _ _ _ 34%nat SB); [img_refl | img_try (clear - FS1 FS2; numconst; img_lia) | img_try (rewrite Z.add_0_l; img_exact (sb_cell X W mem M))].
+ img_apply pairwise_disjoint_of_extents. unfold YF37.REG0, YF37.R_STK, fatom8, YF37.YFRAME, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite (YF37.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew (Ereg regs (YF37.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))) 2 = getr regs 2), SPV.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. split; [|img_try (img_exact (conj I I))]. split; [|img_try (img_exact I)]. clear - S1 S5. numconst. img_lia.
+ split; [|img_try (split; img_exact I)]. cbn [YF37.FFY f_atoms atoms_ok].
set (E0 := Ereg regs (YF37.XW ly (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i))).
assert (E2' : ew E0 2 = w64 sp1) by (img_try (rewrite (YF37.E2 ly regs (SB + b_self b) (zlen (b_items b)) (next_hdr its) (Z.of_nat i) : ew E0 2 = getr regs 2); img_exact R2)).
rewrite region_off_24 in B6, B7. unfold YF37.S7v in Q1, Q2, Q3.
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kBatchSlots, kBatchBytes, kThreadObjSize, kSpaceSize, YF37.YFRAME in *.
split. { img_apply (afact_intro E0 2%nat sp1); [img_try (img_exact E2')| img_try (img_exact U1) | img_try (ceil; clear - CR0 S1 S2 S5; img_lia) | img_try (img_change (2 ^ 4) with 16; img_exact S7') | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro E0 32%nat T); [img_refl | img_try (ceil; clear - CR0 FT1 FT2; img_lia) | img_try (ceil; clear - CR0 FT1 FT2; img_lia) | img_try (img_change (2 ^ 12) with 4096; img_exact FT3) | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro E0 34%nat SB); [img_refl | img_try (ceil; clear - CR0 FS1 FS2; img_lia) | img_try (ceil; clear - CR0 FS1 FS2; img_lia) | img_try (img_change (2 ^ 16) with 65536; img_exact FS3) | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro E0 40%nat (SB + b_self b)); [img_refl | img_try (img_exact B8) | img_try (ceil; clear - CR0 B1 B2; img_lia) | img_try (img_change (2 ^ 13) with 8192; img_exact B3) | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro E0 43%nat (zlen (b_items b))); [img_refl | img_try (ceil; clear - CR0 LENb; img_lia) | img_try (ceil; clear - CR0 LENb; img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro E0 44%nat (next_hdr its)); [img_refl | img_try (img_exact NH3) | img_try (ceil; clear - CR0 NH1; img_lia) | img_try (img_change (2 ^ 4) with 16; img_exact NH2) | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro E0 45%nat (SB + b_self b + 144 + 8 * Z.of_nat i)); [img_refl | img_try (ceil; clear - CR0 Q1 Q2; img_lia) | img_try (ceil; clear - CR0 Q1 Q2; img_lia) | img_try (img_change (2 ^ 3) with 8; img_exact Q3) | img_try (clear; img_lia)]. }
split; [|img_try (img_exact I)]. { img_apply (afact_intro E0 52%nat (Z.of_nat i)); [img_refl | img_try (ceil; clear - CR0 LENi LENb Hi1 Hzi; img_lia) | img_try (ceil; clear - CR0 LENi LENb Hi1 Hzi; img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_try (clear; img_lia)]. }
Qed.
Definition v1 : Z := bv_unsigned (getr regs0 1).
Definition v8 : Z := bv_unsigned (getr regs0 8).   Definition v9 : Z := bv_unsigned (getr regs0 9).
Definition v18 : Z := bv_unsigned (getr regs0 18). Definition v19 : Z := bv_unsigned (getr regs0 19). Definition v20 : Z := bv_unsigned (getr regs0 20).
Definition v21 : Z := bv_unsigned (getr regs0 21). Definition v22 : Z := bv_unsigned (getr regs0 22). Definition v23 : Z := bv_unsigned (getr regs0 23).
Definition v24 : Z := bv_unsigned (getr regs0 24). Definition v25 : Z := bv_unsigned (getr regs0 25).
Lemma seed_Q : forall X t lz qb W regs mem md, qst X t lz qb W regs mem md ->
YF36.free_hyps W ly regs mem (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25.
Proof.
intros X t lz qb W regs mem md ST. destruct ST as [AC RX LEN CR LR FR TM CE].
pose proof (acc_AR _ _ _ _ _ _ _ _ _ _ _ AC) as HAR. destruct HAR as (M & _).
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7').
pose proof (sp1_val regs LR) as SPV. pose proof LR as (R2 & R8 & R9 & R18 & R19 & R21). pose proof CR as (C3 & C4 & C26 & C27).
destruct TM as (T0 & T8 & T16 & T24 & Rlz & Rqb). destruct FR as [CB SV].
assert (Hz : 0 <= zlen t < 2 ^ 40) by (img_try (clear - LEN; unfold YF38.zlen in *; img_lia)).
constructor.
- img_exact (am_layout _ _ _ _ M).
- img_exact IMG.
- rewrite C4. img_exact Etp.
- rewrite SPV. unfold YF36.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by img_lia. split; [img_try (img_exact E1) | img_try (img_exact E2)].
- rewrite SPV. img_exact S7'.
- rewrite SPV. intros a Ha. img_apply (acc_pres _ _ _ _ _ _ _ _ _ _ _ AC). unfold YF38.SY. unfold YF36.YFRAME in Ha. clear - Ha S5; numconst. img_lia.
- rewrite SPV. unfold YF36.YFRAME. rewrite S5. replace (sp0 - 112 + 112) with sp0 by img_lia. splits; assumption.
- unfold v1, w64. rewrite Z_to_bv_bv_unsigned. img_exact Era.
- img_exact Hz.
- unfold v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25. splits; img_apply u64_range.
-
rewrite restrict_mkst_fx. unfold YF36.SS0, YF36.SR0, sr_set. cbn [bv_eqb]. unfold YF36.E0, w64. img_apply (entry_st_ok_full tfxsegs).
+ set (E0 := Ereg regs (YF36.XW (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25)).
assert (HE2 : ew E0 2 = Z_to_bv 64 sp1) by (img_try (rewrite (YF36.E2 regs (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : ew E0 2 = getr regs 2); img_exact R2)).
repeat (img_apply regs_ok_pin; [| img_try (intros XX; discriminate) |]); [img_try (img_apply regs_ok_Ereg) | ..]; cbn [sv_denot].
* rewrite C4, Etp. img_refl.
* rewrite HE2, R8. unfold YF36.YFRAME, w64. rewrite Zbv_add_unsigned. first [img_refl | f_equal; img_lia].
* rewrite R9. img_refl.
* rewrite R18. img_refl.
* rewrite R19. img_refl.
* rewrite R21. img_refl.
+ img_case; vm_compute. all: img_refl.
+ cbn [ms_mem mkst]. set (E0 := Ereg regs (YF36.XW (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25)).
assert (BV2 : bv_unsigned (ew E0 2) = sp1) by (img_try (rewrite (YF36.E2 regs (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : ew E0 2 = getr regs 2); img_exact SPV)).
unfold YF36.REG0, YF36.R_STK, YF36.YFRAME. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
reg_intro. rewrite BV2. split; [img_lia|]. split; [img_try (clear - S2 S5; numconst; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
assert (SVk : forall (k : nat) r (a : Z) k0 (v : Z), nth_error YF34.SAVED k = Some r -> v = bv_unsigned (getr regs0 r) -> a = 104 - 8 * Z.of_nat k ->
ew E0 k0 = w64 v -> YQ0b.chunk_ok tfxsegs E0 (mrestrict (w_H W) mem) sp1 (YQ0b.mkChunk a (CVal 8 (SOff k0 0)))).
{ intros k r a k0 v Hk -> -> Hk0. img_apply (chunk_atom8 E0 _ _ _ k0 (bv_unsigned (getr regs0 r))); [img_try (img_exact Hk0) | img_try (img_apply u64_range) |].
eapply val_mem_addr; [img_try (img_exact (SV k r Hk)) | img_try (rewrite S5; unfold YF38.sp0; img_lia)]. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
* img_apply (chunk_atom8 E0 _ _ _ 46%nat (zlen t)); [img_refl | img_try (clear - Hz; img_lia) | img_try (eapply val_mem_addr; [img_exact T0 | img_lia])].
* img_apply (SVk 0%nat 1%bv _ 50%nat v1); img_refl.
* img_apply (SVk 1%nat 8%bv _ 51%nat v8); img_refl.
* img_apply (SVk 2%nat 9%bv _ 52%nat v9); img_refl.
* img_apply (SVk 3%nat 18%bv _ 53%nat v18); img_refl.
* img_apply (SVk 4%nat 19%bv _ 54%nat v19); img_refl.
* img_apply (SVk 5%nat 20%bv _ 55%nat v20); img_refl.
* img_apply (SVk 6%nat 21%bv _ 56%nat v21); img_refl.
* img_apply (SVk 7%nat 22%bv _ 57%nat v22); img_refl.
* img_apply (SVk 8%nat 23%bv _ 58%nat v23); img_refl.
* img_apply (SVk 9%nat 24%bv _ 59%nat v24); img_refl.
* img_apply (SVk 10%nat 25%bv _ 60%nat v25); img_refl.
+ img_apply pairwise_disjoint_of_extents. cbn. tauto.
+ split; [|img_try (split; img_exact I)]. cbn [YF36.FFQ f_atoms atoms_ok].
set (E0 := Ereg regs (YF36.XW (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25)).
assert (E2' : ew E0 2 = w64 sp1) by (img_try (rewrite (YF36.E2 regs (zlen t) v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : ew E0 2 = getr regs 2); img_exact R2)).
assert (AV : forall k0 v, ew E0 k0 = w64 v -> 0 <= v < 2 ^ 64 -> afact_ok E0 k0 (mkAF 0 (2 ^ 64 - 1) 0)).
{ intros k0 v Hk0 Hv. img_apply (afact_intro E0 k0 v); [img_try (img_exact Hk0) | img_try (img_exact Hv) | img_lia | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, DRSTACK, YF36.YFRAME in *.
split. { img_apply (afact_intro E0 2%nat sp1); [img_try (img_exact E2')| img_try (img_exact U1) | img_try (ceil; clear - CR0 S1 S2 S5; img_lia) | img_try (img_change (2 ^ 4) with 16; img_exact S7') | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro E0 46%nat (zlen t)); [img_refl | img_try (ceil; clear - CR0 Hz; img_lia) | img_try (ceil; clear - CR0 Hz; img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_try (clear; img_lia)]. }
unfold v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25 in *.
splits; try img_exact I; (eapply AV; [img_refl | img_try (img_apply u64_range)]).
Qed.
Lemma seed_E : YF34.free_hyps W0 ly regs0 mem0 (zlen P0).
Proof.
pose proof PRE as (HAR & HRI & HQT & HQG & CELLS & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha1 & Ha2 & LENP & HINIT).
destruct HAR as (M & _). unfold spZ in *.
pose proof entry_facts as (E1 & E2 & E3 & Egp & Etp & Era & E7 & E8). pose proof sp_facts as (S1 & S2 & U0 & U1 & S5 & S6 & S7').
pose proof (T_SB_facts X0 _ M) as (FT1 & FT2 & FT3 & FS1 & FS2 & FS3).
assert (Hz : 0 <= zlen P0 < 2 ^ 40) by (img_try (clear - LENP; unfold YF38.zlen; img_lia)).
assert (VSZ : val_mem tfxsegs (mrestrict (w_H W0) mem0) sp0 8 (zlen P0)).
{ unfold plist_cells, qc_cells in CELLS. apply Forall_cons_iff in CELLS as [C0 _]. cbn [qc_list length] in C0.
pose proof (cell_holds_val_mem B ly (w_H W0) mem0 _ 8 _ C0) as V. cbn [aeval] in V. img_exact V. }
constructor.
- img_exact (am_layout _ _ _ _ M).
- img_exact IMG.
- img_exact Etp.
- split; [img_try (img_exact E1) | img_try (img_exact E2)].
- img_exact E3.
- img_exact HPRES.
- split; [img_try (img_exact Ha1) | img_try (img_exact Ha2)].
- img_exact Era.
- img_exact Hz.
-
rewrite restrict_mkst_fx. unfold YF34.SS0, YF34.SR0, sr_set. cbn [bv_eqb]. unfold YF34.E0, w64, A_DoRecycle. img_apply (entry_st_ok_full tfxsegs).
+ set (E0 := Ereg regs0 (YF34.XW ly (zlen P0))).
repeat (img_apply regs_ok_pin; [| img_try (intros XX; discriminate) |]); [img_try (img_apply regs_ok_Ereg) | ..]; cbn [sv_denot].
* rewrite Etp. img_refl.
* rewrite (YF34.E2 ly regs0 (zlen P0) : ew E0 2 = getr regs0 2), Ha1. rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs0 2)) at 2. rewrite Zbv_add_unsigned, Z.add_0_r. symmetry. img_apply Z_to_bv_bv_unsigned.
* img_change (ew E0 32) with (Z_to_bv 64 T). rewrite Ha2. unfold w64. rewrite Zbv_add_unsigned. img_refl.
+ img_case; vm_compute. all: img_refl.
+ cbn [ms_mem mkst]. set (E0 := Ereg regs0 (YF34.XW ly (zlen P0))).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (YF34.E2 ly regs0 (zlen P0) : ew E0 2 = getr regs0 2); img_refl)).
unfold YF34.REG0, YF34.R_STK, YF34.YFRAME. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
reg_intro. rewrite BV2. split; [img_try (clear - S1; numconst; img_lia)|]. split; [img_try (clear - S2; numconst; img_lia)|]. split.
{ intros o Ho. img_apply apresent_writable; [img_try (clear - Ho S1 S2; numconst; img_lia)|]. img_apply HPRES. clear - Ho. unfold YF38.sp0. numconst. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom8 E0 _ _ _ 46%nat (zlen P0)); [img_refl | img_try (clear - Hz; img_lia) | img_try (eapply val_mem_addr; [img_exact VSZ | img_lia])].
+ img_apply pairwise_disjoint_of_extents. cbn. tauto.
+ split; [|img_try (split; img_exact I)]. cbn [YF34.FFE f_atoms atoms_ok].
set (E0 := Ereg regs0 (YF34.XW ly (zlen P0))).
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite (YF34.E2 ly regs0 (zlen P0) : ew E0 2 = getr regs0 2); unfold w64, YF38.sp0; symmetry; img_apply Z_to_bv_bv_unsigned)).
ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DRSTACK, kThreadObjSize in *.
split. { img_apply (afact_intro E0 2%nat sp0); [img_try (img_exact E2')| img_try (img_exact U0) | img_try (ceil; clear - CR0 S1 S2; img_lia) | img_try (img_change (2 ^ 4) with 16; img_exact E3) | img_try (clear; img_lia)]. }
split. { img_apply (afact_intro E0 32%nat T); [img_refl | img_try (ceil; clear - CR0 FT1 FT2; img_lia) | img_try (ceil; clear - CR0 FT1 FT2; img_lia) | img_try (img_change (2 ^ 12) with 4096; img_exact FT3) | img_try (clear; img_lia)]. }
split; [|img_try (img_exact I)]. { img_apply (afact_intro E0 46%nat (zlen P0)); [img_refl | img_try (ceil; clear - CR0 Hz; img_lia) | img_try (ceil; clear - CR0 Hz; img_lia) | img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_try (clear; img_lia)]. }
Qed.
End e.
End c.
