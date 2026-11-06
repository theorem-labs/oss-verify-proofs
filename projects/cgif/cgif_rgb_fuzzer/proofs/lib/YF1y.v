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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF2d YF0r YF1t YF1p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF07 YF2i YF1s YF2w YF0u YF1a.
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
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. img_refl. Qed.
Lemma same_io_wvb : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. unfold same_io. destruct md; cbn; repeat split; img_refl. Qed.
Section f. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly (0x53244 + D_2c4) regs ch.
Let sp0 : Z := bv_unsigned (getr regs 2).
Hypothesis PRE : acall_pre tfxsegs B ly S W regs mem md ch.
Hypothesis HA0 : getr regs 10 = w64 0.
Hypothesis IA1 : tfx_ialloc_spec.
Hypothesis U1 : tfx_unwind_spec.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation ii := (st_internal_inited S).
Lemma M : ARm B ly S rd0. Proof. img_exact (proj1 (proj1 PRE)). Qed.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 M.
Let LO : layout_ok ly := am_layout B ly S rd0 M.
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Local Notation E0 := (YF2i.E0 ly regs ch).
Local Notation LENv := (YF2i.LENv ly regs ch).
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfx_const ly) e = Some (ACell e w (AV e')) -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. img_exact (tfx_const_lookup_sym B TB ly S H0 mem e w e' M E). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfx_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfxsegs m0 a w x.
Proof. intros a w x E. img_exact (tfx_const_lookup B TB ly S H0 mem a w x M E). Qed.
Lemma cell_state : forall c e (w : nat) e', In c (acells B ly S) -> c = ACell e w (AV e') -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros c e w e' Hin ->. img_apply (cell_holds_val_mem B ly H0 mem e w e'). img_exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 M) _ Hin).
Qed.
Lemma cell_stateZ : forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfxsegs m0 (aeval B ly e) w x.
Proof. intros c e w x Hin E. img_exact (cell_state c e w (ANum x) Hin E). Qed.
Lemma unwinding_val : val_mem tfxsegs m0 (T + t_unwinding) 1 0.
Proof.
replace (T + t_unwinding) with (aeval B ly (AT t_unwinding)) by img_refl.
eapply cell_stateZ; [|img_refl]. unfold acells. rewrite !in_app_iff. do 8 right. left. img_refl.
Qed.
Lemma ial_vals : val_mem tfxsegs m0 TFX_IAL_FLAG 1 (if ii then 1 else 0) /\ val_mem tfxsegs m0 (TFX_IAL_FLAG + 1) 1 0 /\
(if ii then val_mem tfxsegs m0 TFX_IAL_W 8 4096 /\ val_mem tfxsegs m0 (TFX_IAL_W + 8) 8 (TFX_IAL_W + 16)
else val_mem tfxsegs m0 TFX_IAL_W 8 0 /\ val_mem tfxsegs m0 (TFX_IAL_W + 8) 8 0) /\
(forall a, TFX_IAL_LO <= a < TFX_IAL_W \/ TFX_IAL_W + 16 <= a < TFX_IAL_HI -> mbyte tfxsegs m0 a = Some (Z_to_bv 8 0)).
Proof.
assert (IN : forall c, In c (ialloc_cells B S) -> In c (acells B ly S)) by (img_try (intros c Hc; unfold acells; rewrite !in_app_iff; do 7 right; left; img_exact Hc)).
unfold ialloc_cells in IN. rewrite (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB) in IN.
splits.
- replace TFX_IAL_FLAG with (aeval B ly (ANum TFX_IAL_FLAG)) at 1 by img_refl. eapply cell_stateZ; [img_try (img_apply IN; left; img_refl) | img_try (destruct ii; img_refl)].
- replace (TFX_IAL_FLAG + 1) with (aeval B ly (ANum (TFX_IAL_FLAG + 1))) by img_refl. eapply cell_stateZ; [img_try (img_apply IN; right; left; img_refl) | img_refl].
- assert (E1 : aeval B ly (AIal (TFX_IAL_W - TFX_IAL_LO)) = TFX_IAL_W) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)).
assert (E2 : aeval B ly (AIal (TFX_IAL_W - TFX_IAL_LO + 8)) = TFX_IAL_W + 8) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)).
assert (E3 : aeval B ly (AIal (TFX_IAL_W - TFX_IAL_LO + 16)) = TFX_IAL_W + 16) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)).
destruct ii; split.
+ rewrite <- E1. eapply cell_stateZ; [img_try (img_apply IN; do 2 right; left; img_refl) | img_refl].
+ rewrite <- E2, <- E3. eapply cell_state; [img_try (img_apply IN; do 3 right; left; img_refl) | img_refl].
+ rewrite <- E1. eapply cell_stateZ; [img_try (img_apply IN; do 2 right; left; img_refl) | img_refl].
+ rewrite <- E2. eapply (cell_state _ _ 8 (ANum 0)); [img_try (img_apply IN; do 3 right; left; img_refl) | img_refl].
- intros a Ha. pose proof (am_zero B ly S rd0 M) as ZR. unfold ialloc_zero in ZR. rewrite (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB) in ZR.
apply Forall_cons_iff in ZR as [Z1 ZR]. apply Forall_cons_iff in ZR as [Z2 _].
assert (R : rd0 a = Some 0).
{ destruct Ha as [Ha|Ha].
- replace a with (aeval B ly (AIal 0) + (a - TFX_IAL_LO)) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)). img_apply Z1. cbn [snd]. img_lia.
- replace a with (aeval B ly (AIal (TFX_IAL_W - TFX_IAL_LO + 16)) + (a - (TFX_IAL_W + 16))) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)). img_apply Z2. cbn [snd]. img_lia. }
img_exact (aview_byte _ _ _ _ R).
Qed.
Lemma HSP : ly_stk_lo ly + ASTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & Hlo & _ & Hhi & _). unfold spZ in *. unfold sp0. img_lia. Qed.
Lemma IMG : img_cover ly.
Proof. destruct PRE as ((_ & LED & _) & _). img_exact (img_cover_of_ledger ly S md LED). Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) kPtrArrayResv /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) kFakeStackSize /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_stk_lo ly mod 4096 = 0.
Proof. img_exact (YF0u.HIGH B ly S rd0 M IMG). Qed.
Lemma E2 : ew E0 2 = getr regs 2. Proof. img_exact (YF2i.E2 ly regs ch). Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. img_refl. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. img_refl. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. img_refl. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. img_refl. Qed.
Lemma EaIM : ew E0 37 = w64 (0xab3c0 + D_10c0). Proof. img_refl. Qed.
Lemma EaSHB : ew E0 40 = w64 SHADOW_OFF. Proof. img_refl. Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfxsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 0 (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hm)]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SOff k d))).
Proof.
intros base a w k d x Hk Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfxsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfxsegs m0 o.
Proof. intros a w v o Hv Ho Ha. img_apply vis_writable_off; [img_try (img_exact Ha)|]. replace o with (a + (o - a)) by img_lia. eapply val_mem_vis; [img_try (img_exact Hv) | img_lia]. Qed.
Ltac offw := first [ img_lia | img_apply off_img_high; unfold TFX_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; img_lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HI)))))); unfold kThreadObjSize, t_qc, t_unwinding, t_stats, t_cache in *; img_lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Local Ltac lit_region :=
reg_intro; split; [img_lia|]; split; [img_lia|]; split; [img_try (intros o Ho; img_lia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_lit; [img_apply cell_lit; (img_case; vm_compute); img_refl | cbn; img_lia | cbn; img_lia]) |]); img_apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) YF2i.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kHighShadowBeg in hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, S1, S2, T2, T4, T7.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
unfold YF2i.REG0, flit1, flit4, flit8, flits8, fatom8. cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- ASTACK)); [img_try (rewrite E2; img_refl) | img_try (unfold ASTACK in *; img_lia) | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia) | img_try (img_apply HPRES; img_exact Ha)]. }
do 11 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 40%nat 0 SHADOW_OFF); [img_refl | img_try (unfold SHADOW_OFF; img_lia) | | img_try (unfold SHADOW_OFF; cbn; img_lia) | img_try (cbn; img_lia)].
rewrite Z.add_0_l. img_apply cell_lit. img_case; vm_compute. all: img_refl. }
do 13 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. unfold TFX_TP. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit; [| img_try (unfold TFX_TSD; cbn; img_lia) | img_try (cbn; img_lia)].
replace ((6148432 + D_10c0) - 88) with (aeval B ly (ATp (-88))) by (img_try (cbn; rewrite (ts_tp B TB); img_refl)).
replace TFX_TSD with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; unfold TFX_TSD; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. unfold TFX_TSD. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
rewrite Z.add_0_l. replace (6284536 + D_10c0) with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_refl)).
replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply chunk_lit_at; [| img_try (cbn; img_lia) | img_try (cbn; img_lia)]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by img_refl. img_apply (cell_sym (AC 8) 4 (ANum 0)). img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 32%nat 0 T); [img_try (rewrite EaT; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by img_refl. replace T with (aeval B ly (AT 0)) by (img_try (cbn; img_lia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (img_try (cbn; img_lia)). replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [img_try (rewrite EaTOP; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (img_try (cbn; img_lia)). replace (ly_top ly) with (aeval B ly (ATop 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [img_try (rewrite EaTOP; unfold w64; f_equal; img_lia) | img_try (unfold kStackSpan; img_lia) | | img_try (unfold kStackSpan; cbn; img_lia) | img_try (cbn; img_lia)].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (img_try (cbn; img_lia)). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (img_try (cbn; img_lia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply chunk_lit_at; [| img_try (cbn; img_lia) | img_try (cbn; img_lia)]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (img_try (cbn; img_lia)). img_apply (cell_sym (AT 40) 1 (ANum 0)). img_case; vm_compute. all: img_refl. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_unwinding.
pose proof unwinding_val as U. unfold t_unwinding in U.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable _ _ _ _ U); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit_at; [img_try (img_exact U) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 YF2i.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1.
pose proof HSP as [S1 S2].
pose proof (YF0u.SX B ly S rd0 M 2 6 _ _ eq_refl eq_refl ltac:(img_lia)) as DCT.
pose proof (YF0u.SX B ly S rd0 M 6 8 _ _ eq_refl eq_refl ltac:(img_lia)) as DCS.
pose proof (YF0u.SX B ly S rd0 M 2 8 _ _ eq_refl eq_refl ltac:(img_lia)) as DTS.
unfold zdisjoint in DCT, DCS, DTS. cbn [fst snd] in DCT, DCS, DTS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
img_apply pairwise_disjoint_of_extents. unfold YF2i.REG0, flit1, flit4, flit8, flits8, fatom8, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP.
rewrite E2, EaT, EaC. unfold w64.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, ASTACK in *.
fold sp0. rewrite !unsigned_lit_small by img_lia.
clear - S1 S2 hT1 hT2 hC1 hC2 hS1 hS2 hSP1 hSP2 hP1 hP2 Usp DCT DCS DTS CR CR0.
unfold TFX_TP, TFX_TSD, t_unwinding in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in hT1, hC1.
repeat split;
first [ clear DCT DCS DTS hT1 hC1; img_lia
| clear - hT1 CR0; img_lia
| clear - hC1 CR0; img_lia
| clear - hC1 hC2 hT1 hT2 DCT; img_lia
| clear - hC1 hC2 S1 S2 hS1 hS2 Usp DCS; img_lia
| clear - hT1 hT2 S1 S2 hS1 hS2 Usp DTS; img_lia ].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms YF2i.FFN).
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct PRE as (_ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. pose proof (lo_C_al ly LO) as CAL. unfold page_aligned in TAL, T3.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kHighShadowBeg, ASTACK in
hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, S1, S2, T2, T4, T7.
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite E2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (HL : 1 <= LENv <= 30).
{ unfold YF2i.LENv, YF2i.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0.
pose proof (unwind_of_chain_length (0x53244 + D_2c4) ((sp0, bv_unsigned (getr regs 1), bv_unsigned (getr regs 8)) :: ch)) as LEN.
destruct (sp0 + 16 <? ly_top ly); cbn [length]; img_lia. }
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
cbn [YF2i.FFN f_atoms atoms_ok]. unfold aSB, aSHB, aC, aT, aTOP, aLEN, aIM.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 T4 Hal; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
split. { img_apply (AF 32%nat T); [img_try (img_exact EaT)| | | |]. all: clear - CR0 hT1 hT2 TAL; first [img_lia | img_exact TAL]. }
split. { img_apply (AF 33%nat (ly_C ly)); [img_try (img_exact EaC)| | | |]. all: clear - CR0 hC1 hC2 CAL; first [img_lia | img_exact CAL]. }
split. { img_apply (AF 34%nat SB); [img_try (img_exact EaSB)| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [img_lia | img_exact SAL]. }
split. { img_apply (AF 35%nat (ly_top ly)); [img_try (img_exact EaTOP)| | | |]. all: clear - CR0 T1 T2 T3 T4 T7 hS1; unfold ly_bot, kStackSpan in *; first [img_lia | img_exact T3]. }
split. { img_apply (AF 36%nat LENv); [img_try (img_exact EaLEN)| | | |]. all: clear - CR0 HL; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat (0xab3c0 + D_10c0)); [img_try (img_exact EaIM)| | | |]. all: clear; first [img_lia | img_refl]. }
split; [|img_try (img_exact I)]. { img_apply (AF 40%nat SHADOW_OFF); [img_try (img_exact EaSHB)| | | |]. all: clear; unfold SHADOW_OFF; first [img_lia | img_refl]. }
Qed.
Lemma SEED_ok : st_ok tfxsegs E0 YF2i.SS0 (restrict (w_H W) (mkst regs (w64 (0x53100 + D_2c4)) mem (seg_rom tfxsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
rewrite restrict_mkst_fx. unfold YF2i.SS0, YF2i.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; img_exact Htp]) | img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact HA0)].
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- split; [img_try (img_exact FACTS_ok) | img_try (split; img_exact I)].
Qed.
Theorem FH_ok : YF2i.free_hyps W ly regs mem ch ii.
Proof.
pose proof PRE as PRE'. destruct PRE' as ((MM & _ & _) & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). unfold spZ, raZ, s0Z in *. fold sp0 in Hal, Hlo, Hbot, Hhi, HPRES, Hch.
constructor.
- img_exact LO.
- img_exact IMG.
- img_exact HA0.
- rewrite (ts_tp _ TB) in Htp. img_exact Htp.
- img_exact Hra.
- destruct Hch as [R4096 _]. img_exact R4096.
- splits; img_lia.
- img_exact Hal.
- destruct Hch as [_ CH]. unfold frame0_ok, spZ, s0Z in CH. fold sp0 in CH. img_exact CH.
- img_exact ial_vals.
- img_exact IA1.
- img_exact U1.
- img_exact SEED_ok.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfxsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfxsegs H m (a + Z.of_nat kk) = Some (YG0h.le_byte v w kk).
Proof.
intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. img_change (YG0h.le_byte v w kk) with (YP0g.le_byte v w kk). f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ YF2i.WIN ly regs (aeval B ly (c_at c) + i) /\ ~ YF2i.IZONE (aeval B ly (c_at c) + i) /\
0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (YF1t.Tfx_const_loc ly) c Hc) as K. unfold YF1t.const_loc_ok in K.
pose proof FH_ok as FH.
assert (LOW : forall a, YF1t.low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ YF2i.WIN ly regs (a + i) /\ ~ YF2i.IZONE (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold YF1t.low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFX_IMG_LO <= a /\ a + w <= TFX_IAL_LO) \/ (TFX_IAL_HI <= a /\ a + w <= TFX_IAL_FLAG) \/ (TFX_IAL_FLAG + 4 <= a /\ a + w <= TFX_IMG_END) \/
(SHADOW_OFF + TFX_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFX_IMG_END / 8)) by img_lia.
clear L. unfold YF2i.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF in *.
img_change (65536 / 8) with 8192 in R. img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in R.
split; [|img_lia]. destruct R as [R|[R|[R|R]]].
1-3: img_apply (YF2i.notWIN_img W ly regs mem ch ii FH); unfold TFX_IMG_LO, TFX_IMG_END; img_lia.
img_apply (YF2i.notWIN_shb W ly regs mem ch ii FH); unfold kLowShadowBeg, kHighMemBeg; img_lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- pose proof (YF2i.LYB W ly regs mem ch ii FH) as (LB & _). ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [img_try (img_apply (YF2i.notWIN_Thead W ly regs mem ch ii FH); img_lia)|].
unfold YF2i.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. img_lia.
- pose proof (YF2i.LYB W ly regs mem ch ii FH) as (_ & _ & _ & _ & _ & _ & LB & _). ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [img_try (img_apply (YF2i.notWIN_C W ly regs mem ch ii FH); img_lia)|].
unfold YF2i.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- pose proof (YF2i.LYBD W ly regs mem ch ii FH) as (HD1 & HD2 & _). ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HD1, HD2.
split; [img_try (img_apply (YF2i.notWIN_D W ly regs mem ch ii FH); img_lia)|].
unfold YF2i.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. img_lia.
Qed.
Lemma FINH : forall W' c', YF2w.at_RETN W ly regs mem md W' c' -> free_leaf tfxsegs B ly S W regs mem md PNull n (tt, s1) W' c'.
Proof.
intros W' c' HR.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). destruct HAR as (M' & LED & BUD & MW & HSH). clear M'.
destruct HR as (-> & regs' & mem' & mat & -> & CS & MEQ' & UNW & PRES').
set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof HSP as HSP'.
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0u.D B ly sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same. img_apply (proj1 MEQ' (Z_to_bv 64 a)); rewrite unsigned_lit_small by img_exact Ha.
- intros [X|X]; img_apply ND; [img_try (right; left; img_exact X) | img_try (left; img_exact X)].
- intros X. img_apply ND. right; right. unfold YF2i.IZONE in X. unfold YF0u.DI. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB). img_exact X. }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. (subst rd rd'; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (mem' x); discriminate)|].
destruct (mem' x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (img_try ((subst a'; cbv beta); img_apply u64_range)).
assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
assert (NIMG : ~ (0x10000 <= a' < (0x5ff000 + D_1000))).
{ intros X. img_apply (tfx_rom_all a' X). rewrite Ex. img_exact ROM. }
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False).
{ intros m [_ [bb Hb]] Hm. rewrite Ex in Hb. congruence. }
destruct (EM (sp0 - ASTACK) sp0 a') as [C1|C1]. { img_exact (PRX mem' (PRES' a' C1) E'). }
destruct (EM (T + t_unwinding) (T + t_unwinding + 1) a') as [C2|C2].
{ pose proof (UNW 0%nat ltac:(img_lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
replace (ly_T ly + t_unwinding) with a' in U by img_lia. rewrite Ex, Hx, E', ROM in U. discriminate. }
destruct (EM TFX_IAL_LO TFX_IAL_HI a') as [C4|C4]; [img_try (img_apply NIMG; unfold TFX_IAL_LO, TFX_IAL_HI in C4; img_lia)|].
destruct (EM TFX_IAL_FLAG (TFX_IAL_FLAG + 4) a') as [C5|C5]; [img_try (img_apply NIMG; unfold TFX_IAL_FLAG in C5; img_lia)|].
rewrite (proj1 MEQ' x) in E'; [img_try (congruence) | |].
- intros [X|X]; [img_try (img_apply C1) | img_try (img_apply C2)]; img_exact X.
- unfold YF2i.IZONE. tauto. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (img_try (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; img_lia)).
assert (Ux : bv_unsigned x = a) by (img_try ((subst x; cbv beta); img_apply unsigned_lit_small; img_exact Ha')).
assert (PRX : forall m, apresent (w_H W) m a -> False) by (img_try (intros m [Hh _]; fold x in Hh; rewrite Hx in Hh; discriminate)).
assert (C1 : ~ (sp0 - ASTACK <= a < sp0)) by (img_try (intros C1; img_exact (PRX mem' (PRES' a C1)))).
assert (C2 : ~ (T + t_unwinding <= a < T + t_unwinding + 1)).
{ intros C2. pose proof (UNW 0%nat ltac:(img_lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
replace (ly_T ly + t_unwinding) with a in U by img_lia.
rewrite (seg_rom_none_high a ltac:(img_try (clear - Ha; unfold TFX_IMG_END, kLowShadowBeg, kHighShadowEnd in *; img_lia))) in U. fold x in U. rewrite Hx in U. discriminate. }
img_apply (proj1 MEQ' x); rewrite Ux.
- intros [X|X]; [img_try (img_apply C1) | img_try (img_apply C2)]; img_exact X.
- unfold YF2i.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. img_lia. }
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ (subst rd'; cbv beta). rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). img_exact (val_mem_aview _ _ _ _ _ 0 UNW ltac:(img_lia)). }
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B s1) /\ Forall (range_zero B ly rd') (ialloc_zero B)).
{ destruct MEQ' as [_ IP]. unfold YF2i.IAL_POST in IP. cbv zeta in IP. destruct IP as (I1 & I2 & I3 & I4 & I5).
unfold ialloc_cells, ialloc_zero. img_change (st_internal_inited s1) with true. rewrite (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB).
(subst rd'; cbv beta). split.
- img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|img_lia]. img_apply (val_mem_aview _ _ _ _ _ 0 I1). img_lia. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|img_lia]. img_apply (val_mem_aview _ _ _ _ _ 0 I2). img_lia. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFX_IAL_LO + (TFX_IAL_W - TFX_IAL_LO)) with TFX_IAL_W by img_lia.
intros kk Hkk. img_exact (val_mem_aview _ _ _ _ _ kk I3 Hkk). }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFX_IAL_LO + (TFX_IAL_W - TFX_IAL_LO + 8)) with (TFX_IAL_W + 8) by img_lia.
replace (TFX_IAL_LO + (TFX_IAL_W - TFX_IAL_LO + 16)) with (TFX_IAL_W + 16) by img_lia.
intros kk Hkk. img_exact (val_mem_aview _ _ _ _ _ kk I4 Hkk). }
- assert (ZR : forall a0, TFX_IAL_LO <= a0 < TFX_IAL_W \/ TFX_IAL_W + 16 <= a0 < TFX_IAL_HI -> aview tfxsegs (w_H W) mem' a0 = Some 0).
{ intros a0 Ha0. unfold aview. rewrite (I5 a0 Ha0). img_refl. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TB); img_apply ZR; unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W in *; img_lia. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ img_apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const B ly S _ M) c Hc))|].
intros i Hi. (subst rd rd'; cbv beta). destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). img_apply aview_same.
img_apply (proj1 MEQ' (Z_to_bv 64 _)); rewrite unsigned_lit_small by img_exact X3; [img_try (img_exact X1) | img_try (img_exact X2)]. }
pose proof (YF0u.free_finn_ARm B TB ly S rd rd' M Hev sp0 HSP' IMG AG VIS NEW_unw IAL CONST') as MF.
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. img_refl. }
split. 2:{ img_apply (qtight_ext S); [img_refl | img_refl | img_refl | img_try (img_exact HQT)]. }
split; [|img_try (split; [img_apply layout_le_refl | split; [img_apply wle_refl | split; [|split; [|split]]]])].
- split; [img_try (img_exact MF) | img_try (split; [|split; [|split]])].
+ eapply ALedger_same; [img_try (img_exact (YF0u.ALedger_S' ly S tfxsegs md LED)) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
+ destruct BUD as [BUD PIN]. split; [| img_try (img_exact PIN)].
eapply Z.le_trans; [img_try (img_exact BUD) | img_try (img_exact (YF0u.abudget_le S))].
+ eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
+ eapply (ahs_transfer tfxsegs B ly S _ (w_H W) mem mem' (al_img_env tfxsegs ly S md (am_layout B ly S _ M) LED) M HSH VIS HSK).
* eapply (aclient_band_same_frames B ly S); [img_try (img_exact MF) | img_refl].
*   img_refl.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. img_apply AG; [img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)|].
pose proof HI as (_ & _ & _ & _ & hT1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & hS1 & _).
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg. unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize in hT1. unfold kHighMemBeg in hT1, hS1.
unfold YF0u.D, YF0u.DT, YF0u.DS, YF0u.DI. intros [X|[X|X]].
-- clear - X SBg hT1. unfold t_unwinding in X. img_lia.
-- clear - X SBg hS1 HSP'. unfold ASTACK in *. img_lia.
-- rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB) in X. clear - X SBg. unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG in X. img_lia.
- intros r Hr'. img_apply CS. unfold acallee_saved in Hr'. unfold callee_saved. img_lia.
- img_apply same_io_wvb.
- intros a Ha NO NO' NS NE. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
destruct (YF0u.D_owned B TB ly S rd M sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [img_try (img_exact (NO O)) | img_try (img_apply NS; unfold ascratch; left; img_exact O)].
- img_exact PRES'.
Qed.
Theorem afree_null_arm :
amreal tfxsegs (free PNull tr S) W (cfg_at tfxsegs (0x53100 + D_2c4) regs mem md) (free_leaf tfxsegs B ly S W regs mem md PNull n).
Proof.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hev & _).
assert (SPLIT : amreal tfxsegs (ret tt s1) W (cfg_at tfxsegs (0x53100 + D_2c4) regs mem md) (free_leaf tfxsegs B ly S W regs mem md PNull n) ->
amreal tfxsegs (free PNull tr S) W (cfg_at tfxsegs (0x53100 + D_2c4) regs mem md) (free_leaf tfxsegs B ly S W regs mem md PNull n)).
{ intros MAIN. unfold free. cbn [bind ret tick modify mcheck ibind get put set_nev set_internal_inited st_internal_inited].
destruct (st_internal_inited S) eqn:E; cbn [ibind ret modify].
- replace (set_nev (st_nev S + 1) S) with s1; [img_try (img_exact MAIN)|]. unfold s1. generalize E. generalize S. clear. intros S0 E0. destruct S0; cbn in E0 |- *. (subst; cbv beta). img_refl.
- img_exact MAIN. }
img_apply SPLIT. clear SPLIT. cbn [ret amreal].
unfold cfg_at. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- img_exact (YF2w.segN W ly regs mem md ch ii (m_vm_materialized md) FH_ok).
- intros W' c' _ HR. img_exact (FINH W' c' HR).
Qed.
End f.
Theorem afree_null {imgk : img} : forall B, TfxSyms B -> forall ly S W regs mem md n ch,
acall_pre tfxsegs B ly S W regs mem md ch -> getr regs 10 = w64 0 ->
tfx_unwind_spec -> ly_tsd ly = TFX_TSD ->
amreal tfxsegs (free PNull (call_trace ly (0x53244 + D_2c4) regs ch) S) W (cfg_at tfxsegs (0x53100 + D_2c4) regs mem md) (free_leaf tfxsegs B ly S W regs mem md PNull n).
Proof.
intros B TB ly S W regs mem md n ch PRE HA0 U1 HTSD.
img_exact (afree_null_arm B TB ly S W regs mem md n ch PRE HA0 tfx_ialloc_ok U1 HTSD).
Qed.
End b.
