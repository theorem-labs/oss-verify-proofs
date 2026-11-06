(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025), the
   kit the interceptor walks (WrapMallocB*.v, WrapFreeB*.v) take their seeds from: the facts cgif's free / malloc site
   files read off cgif's ARm, read here off ARcf's ARmcf (YG0ncf.v:89-116) and ALedger_cf (YG0ncf.v:254).
   Ported BY STATEMENT, each from its donor, with ARm -> ARmcf (am_const -> amc_const, am_cells -> amc_cells over
   acells_cf, am_layout -> amc_layout) and ALedger -> ALedger_cf (al_img -> alc_img):
   - cf_const_lookup / cf_const_lookup_sym: YF0x.v:210-229 tfib_const_lookup / tfib_const_lookup_sym;
   - cf_cell_state / cf_unwinding_val: YFg3.v:63-73 cell_state / unwinding_val (thread_cells is acells_cf's ninth
     part, as it is acells' ninth, YG0n.v:119-122, YG0ncf.v:50-53);
   - img_cover_of_ledger_cf: YF0x.v:58-65 img_cover_of_ledger;
   - HIGH_cf / SX_cf: YFf0.v:64-69 SX and :106-125 HIGH, whose proofs read only layout_ok and img_cover.
   Reads no listing: no instruction is stepped here. No Admitted / Axiom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x YFl0 YFeq YFex.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* YF0x.v:58-65, al_img -> alc_img. *)
Lemma img_cover_of_ledger_cf : forall ly S md, ALedger_cf tfibsegs ly S md -> img_cover ly.
Proof.
intros ly S md L. split.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_000 ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (alc_img _ _ _ _ L AsanUbsan.AsanUbsan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TFIB_IMG_END. lia.
Qed.

Section k.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (Hp : list Z) (H : word -> bool) (mem : word -> option byte).
Hypothesis M : ARmcf B ly S Hp (aview tfibsegs H mem).

(* YF0x.v:210-219, am_const -> amc_const. *)
Lemma cf_const_lookup : forall a (w : nat) v,
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
val_mem tfibsegs (mrestrict H mem) a w v.
Proof.
intros a w v E.
apply (cell_holds_val_mem B ly H mem (ANum a) w (ANum v)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly)) (amc_const _ _ _ _ _ M)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.

(* YF0x.v:220-229, am_const -> amc_const. *)
Lemma cf_const_lookup_sym : forall e (w : nat) e',
cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros e w e' E.
apply (cell_holds_val_mem B ly H mem e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly)) (amc_const _ _ _ _ _ M)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.

(* YFg3.v:63-66, am_cells over acells -> amc_cells over acells_cf. *)
Lemma cf_cell_state : forall c e (w : nat) e', In c (acells_cf B ly S) -> c = ACell e w (AV e') ->
val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros c e w e' Hin ->. apply (cell_holds_val_mem B ly H mem e w e').
exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M) _ Hin).
Qed.

(* YFg3.v:69-73. *)
Lemma cf_unwinding_val : val_mem tfibsegs (mrestrict H mem) (ly_T ly + t_unwinding) 1 0.
Proof.
replace (ly_T ly + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
apply (cf_cell_state (z1 (AT t_unwinding) 0) (AT t_unwinding) 1 (ANum 0)); [|reflexivity].
unfold acells_cf. rewrite !in_app_iff. do 8 right. left. reflexivity.
Qed.

Lemma cf_layout : layout_ok ly.
Proof. exact (amc_layout _ _ _ _ _ M). Qed.
End k.

Section g.
Variable ly : alayout.
Hypothesis LO : layout_ok ly.
Hypothesis IMG : img_cover ly.
Local Notation T := (ly_T ly).

(* YFf0.v:64-69. *)
Lemma SX_cf : forall i j x y, nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y -> i <> j -> zdisjoint x y.
Proof.
intros i j x y Hi Hj Hne. destruct (Nat.lt_ge_cases i j).
- exact (pairwise_nth zdisjoint _ i j x y (lo_disj _ LO) Hi Hj H).
- pose proof (pairwise_nth zdisjoint _ j i y x (lo_disj _ LO) Hj Hi ltac:(lia)) as Z. unfold zdisjoint in *. lia.
Qed.

(* YFf0.v:106-125. *)
Lemma HIGH_cf : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) (kPtrArrayResv) /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) (kFakeStackSize) /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) (kNodesBlockSize) /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) (kStoreBlockSize) /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) (256) /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_stk_lo ly mod 4096 = 0.
Proof.
pose proof (lo_high _ LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app _ LO) as HA. pose proof (lo_disj _ LO) as HD.
assert (Z3 : forall i x sz, nth_error (owned_extents ly) i = Some (x, sz) -> 0 <= sz -> zone3 x sz).
{ intros i x sz He Hsz. apply (zone3_intro ly x sz IMG Hsz (Forall_nth_f _ _ i _ HA He)).
assert (L : (i < 8)%nat) by (destruct (Nat.lt_ge_cases i 8) as [X|X]; [exact X|]; assert (X' : nth_error (owned_extents ly) i = None) by (apply nth_error_None; cbn; lia); rewrite X' in He; discriminate).
exact (pairwise_ij_f _ _ i (8 - i) _ _ HD ltac:(unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He)
ltac:(unfold static_extents; rewrite nth_error_app2 by (cbn; lia); replace (i + Datatypes.S (8 - i) - length (owned_extents ly))%nat with 1%nat by (cbn; lia); reflexivity)). }
pose proof (Z3 1%nat _ _ eq_refl ltac:(unfold kPtrArrayResv; lia)) as ZQ. pose proof (Z3 2%nat _ _ eq_refl ltac:(unfold kThreadObjSize; lia)) as ZT.
pose proof (Z3 3%nat _ _ eq_refl ltac:(unfold kFakeStackSize; lia)) as ZF. pose proof (Z3 4%nat _ _ eq_refl ltac:(unfold kNodesBlockSize; lia)) as ZNB.
pose proof (Z3 5%nat _ _ eq_refl ltac:(unfold kStoreBlockSize; lia)) as ZSB. pose proof (Z3 6%nat _ _ eq_refl ltac:(lia)) as ZC. clear Z3 HA HD.
pose proof ZQ as (ZQ1 & ZQ2 & _). pose proof ZT as (ZT1 & ZT2 & _). pose proof ZF as (ZF1 & ZF2 & _). pose proof ZNB as (ZNB1 & ZNB2 & _). pose proof ZSB as (ZSB1 & ZSB2 & _). pose proof ZC as (ZC1 & ZC2 & _).
pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_in _ LO) as [S1 S2].
unfold page_aligned in *. splits; try assumption; try lia.
Qed.
End g.
End f.
