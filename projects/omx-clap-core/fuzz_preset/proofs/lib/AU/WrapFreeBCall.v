(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025), the
   CALL SEGMENT of the FREE interceptor over ARcf: __wrap_free's entry (B 0x53820 `j ___interceptor_free`) to
   Deallocate's entry (YB1w's symbol entry tfib_A__ZN6__asan9Allocator10Deallocate..., B 0x32390 = AU/CfImgB.v's
   cf_pc_deallocate), through ___interceptor_free (0x5382c: internal_allocator(), the internal allocator's
   PointerIsMine map test, the BufferedStackTrace set-up, GetMallocContextSize, GetCurrentPc, UnwindImpl) and
   asan_free (0x32368) up to its tail jump `j Deallocate` (0x3238c). Code read: the runtime decode table
   YB1t.tfibtbl_rtF (lib/Reusable/YB1t.v at the base; it covers internal_allocator, asan_free and Deallocate).
   Ported BY STATEMENT from the ARm donors over cgif's ARm on image B:
   - the prefix to UnwindImpl: lib/Reusable/YFga.v:170-342 segA (run to internal_allocator, its spec IA1, the map
     slot region at atom 37, the pins of a1 = p >> 47 = 0 at +0x34 and of a2 = the slot at +0x48, run to UnwindImpl,
     its spec U1), with YFh1.v:119-274 segN's region indices (the seed is YFgn.REG0, WrapFreeBSeed.v) and YFgn's
     IAL-aware window and tail facts (YFgn.v:337-415);
   - the unwinder's return: YFh1.v:275-325 (st_ok_after_call at +0x194, the frame trimmed to [-64, 0)), with the
     stack object's facts kept as YFgc.v:226-242 keeps them;
   - +0x194 to Deallocate's entry: the first run of YFgc.v:191 segB (through asan_free), stopped at Deallocate's entry.
   Callees: internal_allocator() is the donors' named premise IA1 : tfib_ialloc_spec (YFeq.v:144-164, at either value
   of the flag: the init happens here, before asan_free, on every path; discharged by
   YFfg.tfib_ialloc_ok), UnwindImpl is U1 : tfib_unwind_spec (YFl0.v:24; discharged by YFl4.tfib_unwind_ok); the
   InternalFree arm (a pointer of the internal allocator) is refuted as YFga refutes it: the map slot of every
   pointer below 2 ^ 47 reads 0 (the zero part of IAL_POST), and the short-context arm as the seed sets
   B_MALLOC_CONTEXT_SIZE_CELL = 30. TwoLevelMap::Create, GetActuallyAllocatedSize and __lsan_unregister_root_region
   lie on the InternalFree arm and are not reached. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFeq YFgn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import WrapBKit WrapFreeBSeed.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section WK.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Variable mat0 : list word.
Hypothesis PRE : acall_pre_cf tfibsegs B ly S Hp W regs0 mem0 md0 ch.
Hypothesis HP47 : bv_unsigned (getr regs0 10) < 2 ^ 47.
Hypothesis IA1 : tfib_ialloc_spec.
Hypothesis U1 : tfib_unwind_spec.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let cfg0 : config := mkCfg (mkst regs0 (w64 B_WRAP_FREE_PC) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Local Notation E0 := (E0f ly regs0 ch).
Local Notation LENv := (YFgn.LENv ly regs0 ch).
Local Notation tr := (YFgn.tr ly regs0 ch).
Local Notation pa := (bv_unsigned (getr regs0 10)).
Local Notation ii := (st_internal_inited S).

(* The entry facts, from acall_pre_cf (YG0dcf.v:221-250) and TfibSyms. *)
Lemma LY : layout_ok ly. Proof. exact (amc_layout _ _ _ _ _ (proj1 (proj1 PRE))). Qed.
Lemma IMG : img_cover ly. Proof. destruct PRE as ((_ & LED & _) & _). exact (img_cover_of_ledger_cf ly S md0 LED). Qed.
Lemma Hra : YK0s.ret_ok (getr regs0 1). Proof. destruct PRE as (_ & H & _). exact H. Qed.
Lemma Hal : sp0 mod 16 = 0. Proof. destruct PRE as (_ & _ & H & _). exact H. Qed.
Lemma Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & H1 & H2 & H3 & _). unfold spZ in *. unfold sp0. lia. Qed.
Lemma HPRES : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma Hgp : getr regs0 3 = w64 (as_gp B). Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma Htp : getr regs0 4 = w64 TFIB_TP.
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). rewrite (ts_tp _ TB) in H. exact H. Qed.
Lemma Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (H & _) & _). exact H. Qed.
Lemma Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & H) & _). unfold frame0_ok, spZ, s0Z in H. exact H. Qed.

Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 (XWf ly regs0 ch) k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. exact (Er 8 8%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = getr regs0 10. Proof. exact (Er 10 10%bv eq_refl). Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. reflexivity. Qed.
Lemma EaIM : ew E0 37 = w64 (IMf pa). Proof. reflexivity. Qed.
Lemma EaSHB : ew E0 40 = w64 SHADOW_OFF. Proof. reflexivity. Qed.
(* The pointer's map slot lies in the internal allocator's zero zone, below its word at TFIB_IAL_W (YFgi.v's
   derived_ranges for IMv). *)
Lemma IMR : 0 <= pa < 2 ^ 47 /\ TFIB_IAL_LO <= IMf pa /\ IMf pa + 16 <= TFIB_IAL_W /\
B_INTERNAL_ALLOC_PLACEHOLDER_CELL <= IMf pa <= B_INTERNAL_ALLOC_PLACEHOLDER_CELL + 8 * 0x7fff /\ IMf pa mod 8 = 0.
Proof.
assert (H0 : 0 <= pa < 2 ^ 47) by (split; [apply u64_range | exact HP47]).
unfold IMf, B_INTERNAL_ALLOC_PLACEHOLDER_CELL, TFIB_IAL_LO, TFIB_IAL_W. lia.
Qed.

(* YFg3.v:63-99 in the cf form: the internal allocator's cells (ialloc_cells, the eighth part of acells_cf,
   lib/Reusable/YG0ncf.v) and its zero zone (amc_zero) at the caller's state. *)
Lemma cell_state : forall c e (w : nat) e', In c (acells_cf B ly S) -> c = ACell e w (AV e') ->
val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros c e w e' Hin E. exact (cf_cell_state B ly S Hp (w_H W) mem0 (proj1 (proj1 PRE)) c e w e' Hin E). Qed.
Lemma cell_stateZ : forall c e (w : nat) x, In c (acells_cf B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. intros c e w x Hin E. exact (cell_state c e w (ANum x) Hin E). Qed.
Lemma ial_vals : val_mem tfibsegs m0 TFIB_IAL_FLAG 1 (if ii then 1 else 0) /\ val_mem tfibsegs m0 (TFIB_IAL_FLAG + 1) 1 0 /\
(if ii then val_mem tfibsegs m0 TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16)
else val_mem tfibsegs m0 TFIB_IAL_W 8 0 /\ val_mem tfibsegs m0 (TFIB_IAL_W + 8) 8 0) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m0 a = Some (Z_to_bv 8 0)).
Proof.
assert (IN : forall c, In c (ialloc_cells B S) -> In c (acells_cf B ly S)) by (intros c Hc; unfold acells_cf; rewrite !in_app_iff; do 7 right; left; exact Hc).
unfold ialloc_cells in IN. rewrite (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB) in IN.
split; [|split; [|split]].
- replace TFIB_IAL_FLAG with (aeval B ly (ANum TFIB_IAL_FLAG)) at 1 by reflexivity. eapply cell_stateZ; [apply IN; left; reflexivity | destruct ii; reflexivity].
- replace (TFIB_IAL_FLAG + 1) with (aeval B ly (ANum (TFIB_IAL_FLAG + 1))) by reflexivity. eapply cell_stateZ; [apply IN; right; left; reflexivity | reflexivity].
- assert (E1 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO)) = TFIB_IAL_W) by (cbn; rewrite (ts_ial_lo _ TB); lia).
assert (E2 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 8)) = TFIB_IAL_W + 8) by (cbn; rewrite (ts_ial_lo _ TB); lia).
assert (E3 : aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 16)) = TFIB_IAL_W + 16) by (cbn; rewrite (ts_ial_lo _ TB); lia).
destruct ii; split.
+ rewrite <- E1. eapply cell_stateZ; [apply IN; do 2 right; left; reflexivity | reflexivity].
+ rewrite <- E2, <- E3. eapply cell_state; [apply IN; do 3 right; left; reflexivity | reflexivity].
+ rewrite <- E1. eapply cell_stateZ; [apply IN; do 2 right; left; reflexivity | reflexivity].
+ rewrite <- E2. eapply (cell_state _ _ 8 (ANum 0)); [apply IN; do 3 right; left; reflexivity | reflexivity].
- intros a Ha. pose proof (amc_zero B ly S Hp _ (proj1 (proj1 PRE))) as ZR. unfold ialloc_zero in ZR. rewrite (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB) in ZR.
apply Forall_cons_iff in ZR as [Z1 ZR]. apply Forall_cons_iff in ZR as [Z2 _].
assert (R : aview tfibsegs (w_H W) mem0 a = Some 0).
{ destruct Ha as [Ha|Ha].
- replace a with (aeval B ly (AIal 0) + (a - TFIB_IAL_LO)) by (cbn; rewrite (ts_ial_lo _ TB); lia). apply Z1. cbn [snd]. lia.
- replace a with (aeval B ly (AIal (TFIB_IAL_W - TFIB_IAL_LO + 16)) + (a - (TFIB_IAL_W + 16))) by (cbn; rewrite (ts_ial_lo _ TB); lia). apply Z2. cbn [snd]. lia. }
exact (aview_byte _ _ _ _ R).
Qed.

(* YFgn.v:125-149 LYB, :167-184 LYD, :185-200 iv_vs_stack / stack_ivs, from layout_ok and img_cover alone. *)
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\
zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly.
Proof.
pose proof LY as LY. pose proof IMG as IMG.
pose proof (lo_high ly LY) as IP. pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth_f _ _ 6 _ HA eq_refl) as IC.
pose proof (Forall_nth_f _ _ 4 _ HA eq_refl) as INB. pose proof (Forall_nth_f _ _ 5 _ HA eq_refl) as ISB.
cbn beta in IT, IC, INB, ISB. cbn [fst snd] in IT, IC, INB, ISB.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear_all; lia) IC (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_NB ly) kNodesBlockSize IMG ltac:(clear_all; unfold kNodesBlockSize; lia) INB (pairwise_ij_f _ _ 4 4 _ _ HD eq_refl eq_refl)) as ZNB.
pose proof (zone3_intro ly (ly_SB ly) kStoreBlockSize IMG ltac:(clear_all; unfold kStoreBlockSize; lia) ISB (pairwise_ij_f _ _ 5 3 _ _ HD eq_refl eq_refl)) as ZSB.
clear HA HD. unfold in_high in IP. cbn [fst snd] in IP. unfold T, SB in *.
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia|].
split; [clear - IP; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia|]. split; [clear - HSP; lia|]. split; [clear - HSP; lia|]. split; [clear - IP; lia|].
split; [exact ZC|]. split; [clear - ZC; unfold zone3 in ZC; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia|].
split; [exact ZNB|]. split; [clear - ZNB; unfold zone3 in ZNB; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia|].
split; [exact ZSB|]. split; [clear - ZSB; unfold zone3 in ZSB; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia|].
clear - T1 T2 T3 T4 T5 T6 T7. repeat split; lia.
Qed.
Lemma LYD :
let P := (ly_prim ly, kPrimResvSize) in let Tt := (ly_T ly, kThreadObjSize) in let NB := (ly_NB ly, kNodesBlockSize) in
let SBb := (ly_SB ly, kStoreBlockSize) in let C := (ly_C ly, 256) in let STK := (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) in
(zdisjoint P Tt /\ zdisjoint P NB /\ zdisjoint P SBb /\ zdisjoint P C /\ zdisjoint P STK) /\
(zdisjoint Tt NB /\ zdisjoint Tt SBb /\ zdisjoint Tt C /\ zdisjoint Tt STK) /\
(zdisjoint NB SBb /\ zdisjoint NB C /\ zdisjoint NB STK) /\ (zdisjoint SBb C /\ zdisjoint SBb STK) /\ zdisjoint C STK.
Proof.
pose proof LY as LY.
pose proof (lo_disj ly LY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & DF & DNB & DSB & DC & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [PNB DP]. apply Forall_cons_iff in DP as [PSB DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TNB DT]. apply Forall_cons_iff in DT as [TSB DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DNB as [NBSB DNB]. apply Forall_cons_iff in DNB as [NBC DNB]. apply Forall_cons_iff in DNB as [_ DNB]. apply Forall_cons_iff in DNB as [NBSTK _].
apply Forall_cons_iff in DSB as [SBC DSB]. apply Forall_cons_iff in DSB as [_ DSB]. apply Forall_cons_iff in DSB as [SBSTK _]. apply Forall_cons_iff in DC as [_ DC]. apply Forall_cons_iff in DC as [CSTK _].
cbn zeta. repeat split; assumption.
Qed.
Lemma iv_vs_stack : forall lo len, zdisjoint (lo, len) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ->
ly_stk_lo ly <= sp0 - ASTACK -> sp0 <= ly_stk_hi ly -> lo + len <= sp0 - ASTACK \/ sp0 <= lo.
Proof. intros lo len D H1 H2. unfold zdisjoint in D. cbn [fst snd] in D. lia. Qed.
Lemma stack_ivs :
(T + kThreadObjSize <= sp0 - ASTACK \/ sp0 <= T) /\ (ly_prim ly + kPrimResvSize <= sp0 - ASTACK \/ sp0 <= ly_prim ly) /\
(ly_C ly + 256 <= sp0 - ASTACK \/ sp0 <= ly_C ly) /\ (ly_NB ly + kNodesBlockSize <= sp0 - ASTACK \/ sp0 <= ly_NB ly) /\
(ly_SB ly + kStoreBlockSize <= sp0 - ASTACK \/ sp0 <= ly_SB ly).
Proof.
pose proof LYD as ((_ & _ & _ & _ & PSTK) & (_ & _ & _ & TSTK) & (_ & _ & NBSTK) & (_ & SBSTK) & CSTK).
pose proof Hsp as (S1 & S2 & S3).
assert (A1 : ly_stk_lo ly <= sp0 - ASTACK) by lia. assert (A2 : sp0 <= ly_stk_hi ly) by lia.
split; [exact (iv_vs_stack _ _ TSTK A1 A2)|]. split; [exact (iv_vs_stack _ _ PSTK A1 A2)|]. split; [exact (iv_vs_stack _ _ CSTK A1 A2)|].
split; [exact (iv_vs_stack _ _ NBSTK A1 A2)|]. exact (iv_vs_stack _ _ SBSTK A1 A2).
Qed.

(* YFgn.v:201-265: the seed's writable windows (the stack window and T + t_unwinding). *)
Definition WIN (a : Z) : Prop := (sp0 - ASTACK <= a < sp0) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Lemma WSKEL_WIN : forall (E : env) a t,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> In t YFgn.WSKEL ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Proof.
intros E a t HE Hin Hr. pose proof LYB as HF.
unfold YFgn.WSKEL in Hin. cbn [In] in Hin. unfold WIN.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, aHAVf, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by (cbv; lia);
rewrite ?E2, ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0, T in *; lia.
Qed.
Lemma windows_WIN : forall (E : env) rs a,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (YFgn.win_sub t) YFgn.WSKEL || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub).
assert (SUB : forall E' a' t u', YFgn.win_sub t u' = true ->
base_val E' (fst (fst t)) + snd (fst t) <= a' < base_val E' (fst (fst t)) + snd t ->
base_val E' (fst (fst u')) + snd (fst u') <= a' < base_val E' (fst (fst u')) + snd u').
{ clear. intros E' a' [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold YFgn.win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. subst. lia.
- lia. }
exact (WSKEL_WIN E a u HE Hinu (SUB E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma WIN_zone : forall a, WIN a -> ~ (TFIB_IMG_LO <= a < TFIB_IMG_END) /\ ~ (kLowShadowBeg <= a < kHighMemBeg) /\ 0 <= a < 2 ^ 64.
Proof.
intros a Hw. pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & HF). pose proof Hsp as (S1 & S2 & S3).
unfold WIN in Hw. destruct Hw as [Hs | Ht].
- clear - Hs S1 S2 S3 HF. ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. lia.
- clear - Ht F1. ceil; unfold zone3, zone3cases, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. unfold T in *. lia.
Qed.
Lemma WIN_not_high : forall a, sp0 <= a < ly_top ly -> ~ WIN a.
Proof.
intros a Ha Hw. pose proof LYB as HF. pose proof Hsp as (S1 & S2 & S3).
destruct Hw as [Hs | Ht].
- unfold ASTACK in *. lia.
- pose proof LYD as (_ & (_ & _ & _ & TSTK) & _ & _ & _). unfold zdisjoint in TSTK. cbn [fst snd] in TSTK.
unfold kThreadObjSize, ASTACK, t_unwinding in *. unfold T in *. lia.
Qed.
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. intros E r rs H. induction rs as [|r' rs IH]; cbn; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx]. Qed.
Lemma kept_of_frame : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply mbyte_mrestrict_same. apply Hfr. rewrite unsigned_lit_small by lia. exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. apply apresent_writable_off; [exact Hh|]. apply Hpr. apply writable_off_apresent; [exact Hh | exact Hw].
Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 LYB) Ha). Qed.
Lemma off_C : forall a, ly_C ly <= a < ly_C ly + 256 -> off_img a.
Proof. intros a Ha. pose proof LYB as (_ & _ & _ & _ & _ & _ & F7 & _). exact (zone3_off_img _ _ a F7 Ha). Qed.
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; unfold kThreadObjSize; tac | apply off_C; tac
| unfold off_img; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; unfold TFIB_IMG_LO; unfold YImgTop.IMG_LO_B in *; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; tac ].

Lemma kept_of_frame_hi : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, off_img a -> apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply mbyte_mrestrict_same. apply Hfr. rewrite unsigned_lit_small by lia. exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. apply apresent_writable_off; [exact Hh|]. apply Hpr; [exact Hh|]. apply writable_off_apresent; [exact Hh | exact Hw].
Qed.
(* YFgn.v:326-336. *)
Lemma pres_off_of_frame : forall (m m1 : word -> option byte) (X : Z -> Prop),
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, X a -> TFIB_IMG_LO <= a) ->
(forall a, TFIB_IMG_END <= a < 2 ^ 64 -> apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
forall a, off_img a -> apresent (w_H W) m a -> apresent (w_H W) m1 a.
Proof.
set (Hd := w_H W). clearbody Hd. clear_all.
intros m m1 X Hfr HX Hpr a [Hlo|Hhi] Hp; [|exact (Hpr a Hhi Hp)].
destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply Hfr.
rewrite unsigned_lit_small by (unfold TFIB_IMG_LO in Hlo; unfold YImgTop.IMG_LO_B in *; lia). intros HXa. pose proof (HX _ HXa). lia.
Qed.

(* YFgn.v:337-386 IZONE, RFACTS, zone_lit / zone_T / zone_C, tail_facts: with the internal allocator's zone. *)
Definition IZONE (a : Z) : Prop := (TFIB_IAL_LO <= a < TFIB_IAL_HI) \/ (TFIB_IAL_FLAG <= a < TFIB_IAL_FLAG + 4).
Definition RFACTS (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - ASTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFIB_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFIB_IMG_LO)) /\
((hi <= TFIB_IAL_LO \/ TFIB_IAL_HI <= lo) /\ (hi <= TFIB_IAL_FLAG \/ TFIB_IAL_FLAG + 4 <= lo)).
Lemma zone_lit : forall lo hi wlo whi,
TFIB_IMG_LO <= lo -> hi <= TFIB_IMG_END -> (hi <= TFIB_IAL_LO \/ TFIB_IAL_HI <= lo) -> (hi <= TFIB_IAL_FLAG \/ TFIB_IAL_FLAG + 4 <= lo) ->
whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3 Hz5.
pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & T3 & T4 & T5). pose proof Hsp as (S1 & S2 & S3).
unfold RFACTS; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. clear - Hz0 Hz1 Hz2 Hz3 Hz5 T1 T5 S1. numconst. unfold sp0 in *. lia.
Qed.
Lemma zone_T : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof LYB as (F1 & _).
pose proof stack_ivs as (IT & _).
unfold RFACTS; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. clear - Hz0 Hz1 Hz2 F1 IT. numconst. unfold T, sp0 in *. lia.
Qed.
Lemma zone_C : forall lo hi wlo whi,
ly_C ly <= lo -> hi <= ly_C ly + 256 -> (whi <= wlo \/ (ly_C ly <= wlo /\ whi <= ly_C ly + 256)) -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof LYB as (_ & _ & _ & _ & _ & _ & F7 & _).
pose proof stack_ivs as (_ & _ & IC & _).
unfold RFACTS; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. clear - Hz0 Hz1 Hz2 F7 IC. numconst. unfold sp0 in *. lia.
Qed.
Lemma tail_facts : forall (E : env) r,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> In (skel r) YFgn.SKEL_TAIL ->
let b := base_val E (YP09.r_base r) in
(b + YP09.r_hi r <= sp0 - ASTACK \/ sp0 <= b + YP09.r_lo r) /\ 0 <= b + YP09.r_lo r /\ b + YP09.r_hi r <= 2 ^ 64 /\
(YP09.r_whi r <= YP09.r_wlo r \/ (TFIB_IMG_END <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= 2 ^ 64) \/ (0 <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= TFIB_IMG_LO)) /\
((b + YP09.r_hi r <= TFIB_IAL_LO \/ TFIB_IAL_HI <= b + YP09.r_lo r) /\ (b + YP09.r_hi r <= TFIB_IAL_FLAG \/ TFIB_IAL_FLAG + 4 <= b + YP09.r_lo r)).
Proof.
intros E r HE Hin. pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & LB).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
let sk := eval vm_compute in YFgn.SKEL_TAIL in change YFgn.SKEL_TAIL with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (clear - HE; cbv; lia); rewrite ?E2, ?EaT, ?EaC, ?EaSHB; unfold w64;
rewrite ?unsigned_lit_small by (clear - F1 F7; numconst; unfold T in *; lia).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) /\ ?R =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D) /\ R)
by (clear - RF; destruct RF as (X1 & X2 & X3 & X4 & X5); refine (conj X1 (conj X2 (conj X3 (conj _ X5)))); clear - X4; unfold zone3, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia) end.
all: first [ apply zone_lit; clear; numconst; unfold TFIB_TSD, TFIB_TP; lia
| apply zone_T; clear - F1 F2; numconst; unfold T in *; lia
| apply zone_C; clear - F7 F8; numconst; lia ].
Qed.

(* YFgn.v:387-415: the memory frame of the walk (outside the windows and the internal allocator's zone) and the
   internal allocator's state after its init (IAL_POST, the post of IA1). *)
Definition MEQ (m : word -> option byte) : Prop := forall x : word, ~ WIN (bv_unsigned x) -> ~ IZONE (bv_unsigned x) -> m x = mem0 x.
Definition IAL_POST (m : word -> option byte) : Prop :=
let m' := mrestrict (w_H W) m in
val_mem tfibsegs m' TFIB_IAL_FLAG 1 1 /\ val_mem tfibsegs m' (TFIB_IAL_FLAG + 1) 1 0 /\
val_mem tfibsegs m' TFIB_IAL_W 8 4096 /\ val_mem tfibsegs m' (TFIB_IAL_W + 8) 8 (TFIB_IAL_W + 16) /\
(forall a, TFIB_IAL_LO <= a < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a < TFIB_IAL_HI -> mbyte tfibsegs m' a = Some (Z_to_bv 8 0)).
Definition MEQI (m : word -> option byte) : Prop := MEQ m /\ IAL_POST m.
Lemma MEQI_frame : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (YFgn.win_sub t) YFgn.WSKEL || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> MEQI m -> MEQI m'.
Proof.
intros E rs m m' HE Hb HF [M I].
assert (LOWEQ : forall a, IZONE a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
{ intros a Ha. apply HF. intros Hw.
unfold IZONE in Ha. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Ha.
pose proof (WIN_zone _ (windows_WIN E rs _ HE Hb Hw)) as (Hh & _). rewrite unsigned_lit_small in Hh by lia.
apply Hh. unfold zone3, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. lia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). apply HF. intros Hw. apply Hx. exact (windows_WIN E rs _ HE Hb Hw).
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold IAL_POST.
assert (V : forall a (n : nat) v, (forall k, (k < n)%nat -> IZONE (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict (w_H W) m) a n v -> val_mem tfibsegs (mrestrict (w_H W) m') a n v).
{ intros a n v Hz Hv. eapply val_mem_frame; [|exact Hv]. intros k Hk. apply LOWEQ, Hz, Hk. }
unfold IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W in *.
split; [apply V; [intros k Hk; lia | exact I1]|]. split; [apply V; [intros k Hk; lia | exact I2]|].
split; [apply V; [intros k Hk; lia | exact I3]|]. split; [apply V; [intros k Hk; lia | exact I4]|].
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) m m' a) by (apply LOWEQ; lia). apply I5. exact Ha.
Qed.
Ltac meq_acc HE :=
match goal with
| M : MEQI ?ma, HFx : frame_of ?E ?rs ?ma ?mb |- _ =>
let M2 := fresh "MQ" in
pose proof (MEQI_frame E rs ma mb HE ltac:(vm_compute; reflexivity) HFx M) as M2;
clear M HFx; try match goal with HFr : frame_of E rs (mrestrict _ ma) (mrestrict _ mb) |- _ => clear HFr end
end.

(* The state at Deallocate's entry: asan_free's tail call Deallocate(&instance, p, 0, 0, &stack, FROM_MALLOC)
   with ra the return into ___interceptor_free (+0x1a8, after its `jal asan_free` at +0x1a4), sp the interceptor's
   (its frame is 0x7f0 + 0x60 = 2128 bytes; asan_free has none), the stack object at sp (trace pointer, length,
   trace), the interceptor's saved registers, the callee-saved registers the segment keeps, the memory frame (MEQ:
   changed only in the caller's stack window, T + t_unwinding and the internal allocator's zone), the internal
   allocator initialized (IAL_POST), T + t_unwinding at 0 and the caller's stack window present. *)
Definition at_DEALLOC (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regsD memD mat,
c' = mkCfg (mkst regsD (w64 tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE) memD (seg_rom tfibsegs))
  (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regsD 1 = w64 (B_INTERCEPTOR_FREE_PC + 0x1a8) /\ getr regsD 2 = w64 (sp0 - 2128) /\
getr regsD 10 = w64 TFIB_INST /\ getr regsD 11 = getr regs0 10 /\ getr regsD 12 = w64 0 /\
getr regsD 13 = w64 0 /\ getr regsD 14 = w64 (sp0 - 2128) /\ getr regsD 15 = w64 1 /\
getr regsD 8 = getr regs0 2 /\ getr regsD 3 = getr regs0 3 /\ getr regsD 4 = w64 TFIB_TP /\
(forall r : Z, 22 <= r <= 27 -> getr regsD (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) /\
MEQI memD /\
val_mem tfibsegs (mrestrict (w_H W) memD) (T + t_unwinding) 1 0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) memD a) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 2128) 8 (sp0 - 2112) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 2120) 8 LENv /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 2112 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (sp0 - 56) 8 (bv_unsigned (getr regs0 21)).

Lemma seg_call : SRr tfibsegs W cfg0 at_DEALLOC.
Proof.
pose proof Hwx_tfa as Hwx. pose proof (SEED_ok B TB ly S Hp W regs0 mem0 md0 ch PRE HP47) as HS.
pose proof Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof LY as LY. pose proof IMG as IMG.
pose proof Hal as Hsp_al. pose proof Hch as Hch. pose proof Hra4096 as Hra4096. pose proof IMR as IMR.
pose proof ial_vals as HIAL.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
(* YFga.v:175-199: the run to internal_allocator(), and its spec IA1 at the caller's flag. *)
srr_run_to_sh tfibtbl_rtF_ok HS B_INTERNAL_ALLOCATOR_PC.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite E2 in R2.
eapply SRr_bind.
{ destruct HIAL as (IA & IB & IC & ID).
assert (FR : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ms_mem ms (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ha. apply HF. intros Hw.
lazymatch type of Hw with in_wrange _ ?rs _ =>
pose proof (WIN_zone _ (windows_WIN E0 rs _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw)) as (X & _) end.
rewrite unsigned_lit_small in X by (unfold zone3, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END in Ha; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia). exact (X Ha). }
apply (IA1 W (ms_regs ms) (ms_mem ms) _ ii).
- rreg HS (1%bv : bv 5) R1; rewrite R1. apply YK0s.ret_ok_even. reflexivity.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; lia).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp_al.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; lia). numconst; lia.
- rewrite R2. unfold w64. rewrite unsigned_lit_small by (numconst; lia). numconst; lia.
- intros a Ha. rewrite R2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (numconst; lia).
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; numconst; lia
| off_by ltac:(numconst; lia) ].
- eapply val_mem_frame; [|exact IA]. intros k Hk. apply FR; numconst; lia.
- eapply val_mem_frame; [|exact IB]. intros k Hk. apply FR; numconst; lia.
- memv HS 21%nat 0%nat; [reflexivity | reflexivity | lia].
- memv HS 22%nat 0%nat; [reflexivity | reflexivity | lia].
- destruct ii; destruct IC as [IC1 IC2]; split; (eapply val_mem_frame; [|eassumption]); intros k Hk; apply FR; numconst; lia.
- intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) mem0 (ms_mem ms) a) by (apply FR; numconst; lia). apply ID. exact Ha. }
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & H10r & Hfr & Hpr & IV1 & IV2 & IV3 & IV4 & IV5). srr_norm_model.
rreg HS (1%bv : bv 5) R1.
(* YFh1.v:151-183: the regions after the call (the frame above sp0 - 2128 and the tail kept), the scratch window. *)
set (X1 := fun a : Z => (sp0 - 2176 <= a < sp0 - 2128) \/ IZONE a).
assert (Hfr' : forall x : word, ~ X1 (bv_unsigned x) -> mem1 x = ms_mem ms x).
{ intros x Hx. subst X1. unfold IZONE in Hx. rewrite R2 in Hfr. unfold w64 in Hfr. rewrite unsigned_lit_small in Hfr by (numconst; lia).
apply Hfr; unfold IAL_STK in *; tauto || (intros HH; apply Hx; tauto) || lia. }
jafter_call2 HS 54%nat regs1 (mrestrict (w_H W) mem1) HP (-2128) (seq 0 36) HS1.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ constructor;
[ eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:(subst X1; unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; lia) Hpr)); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite E2; subst X1; unfold IZONE; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; lia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with YFgn.SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts E0 r (fun k _ => eq_refl) Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
eapply (kept_of_frame_hi E0 _ _ X1 _ Hfr' (pres_off_of_frame _ _ X1 Hfr' ltac:(subst X1; unfold IZONE; intros a Ha; clear - Ha Usp Hlo LB; numconst; lia) Hpr)); intros a Ha; subst X1; unfold IZONE; cbn beta; clear - Ha Y1 Y2 Y3 Y4 Y5; numconst; lia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. apply Hpr; [clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; lia|]. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; numconst; lia | off_by ltac:(numconst; lia) ]. }
set (En1 := havoc E0 54 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < aHAVf)%nat -> ew En1 k = ew E0 k) by (intros k Hk; subst En1; apply ew_havoc_old; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat ltac:(cbv; lia)), E2; unfold IFRAME;
split; [numconst; lia|]; split; [numconst; lia|]; split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(numconst; lia) | apply PRES1; numconst; lia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; lia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with YFgn.SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; lia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; lia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
(* YFga.v:237-256: the pointer's map slot (atom 37), 8 zero bytes at +8 (IAL_POST's zero zone), and a0 =
   TFIB_IAL_LO, internal_allocator()'s result. *)
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 37%nat) 8 16 0 0 [YP09.mkChunk 8 (CZero 8)])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 37%nat ltac:(cbv; lia)), EaIM; unfold w64; rewrite unsigned_lit_small by (clear - IMR; numconst; lia);
split; [lia|]; split; [clear - IMR; numconst; lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil]; intros i Hi; cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len YP09.cbyte] in Hi |- *;
exists (Z_to_bv 8 0); split; [reflexivity|]; apply IV5; clear - Hi IMR; numconst; lia
| apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 37%nat ltac:(cbv; lia)), (HEn1 2%nat ltac:(cbv; lia)), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (clear - IMR; numconst; lia); clear - IMR Usp Hlo LB; numconst; lia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 37%nat ltac:(cbv; lia)), (HEn1 2%nat ltac:(cbv; lia)), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (clear - IMR; numconst; lia); clear - IMR Usp Hlo LB; numconst; lia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with YFgn.SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 37%nat ltac:(cbv; lia)), EaIM;
unfold w64; rewrite unsigned_lit_small by (clear - IMR; numconst; lia); clear - Y5 IMR; numconst; lia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
apply (st_ok_pin_reg _ _ _ 10%bv (SLit TFIB_IAL_LO)) in HS1; [| intros X; discriminate | cbn [sv_denot ms_regs]; symmetry; exact H10r].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
assert (MEQ1 : MEQI mem1).
{ split.
- intros x Hx Hz. rewrite Hfr' by (subst X1; cbn beta; intros [HH|HH]; [apply Hx; left; unfold ASTACK; lia | exact (Hz HH)]).
apply HF. intros Hw. apply Hx. exact (windows_WIN E0 (ss_mem SS0f) _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw).
- exact (conj IV1 (conj IV2 (conj IV3 (conj IV4 IV5)))). }
clear HF HFr Hfr Hfr'.
(* YFga.v:264-276: the pointer's high bits (a1 = p >> 47 = 0 at +0x34), its map slot (a2 at +0x48), the run to the
   unwinder. *)
srr_run_sh tfibtbl_rtF_ok HS. meq_acc HEn1.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear HS; numconst. pin_zev. rewrite (HEn1 10%nat ltac:(cbv; lia)), E10.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS B_INTERCEPTOR_FREE_PC_OFF_48. meq_acc HEn1.
apply (st_ok_pin_regU _ _ _ 12%bv (SOff 37%nat 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear HS; numconst. pin_zev. rewrite (HEn1 10%nat ltac:(cbv; lia)), (HEn1 37%nat ltac:(cbv; lia)), E10, EaIM. unfold w64.
unfold IMf, B_INTERNAL_ALLOC_PLACEHOLDER_CELL in *. rewrite !unsigned_lit_small by lia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. change (2 ^ 32) with 4294967296 in *.
zcanon_simp. lia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtF_ok HS B_UNWINDIMPL_PC. meq_acc HEn1.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msU end.
match goal with M : MEQI (ms_mem msU) |- _ => rename M into MEQU end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En1 _ _ HS eq_refl) as Hshape2; cbn [ss_pc] in Hshape2. rewrite Hshape2.
rreg HS (2%bv : bv 5) Q2. rewrite (HEn1 2%nat ltac:(cbv; lia)), E2 in Q2.
assert (PRES2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msU) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)).
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; lia)), E2; numconst; lia | off_by ltac:(numconst; lia) ].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; lia)), E2; numconst; lia | off_by ltac:(numconst; lia) ]. }
(* OBJ0 and Z8 of YFgc.segB (lib/Reusable/YFgc.v), read before the call: the stack object's trace pointer, and its length word still 0. *)
assert (OBJ0p : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2128) 8 (sp0 - 2112)).
{ memv HS 2%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia
| cbn [sv_denot]; rewrite (HEn1 2%nat ltac:(cbv; lia)), E2; f_equal; unfold sp0; lia | clear - Usp Hlo LB; numconst; lia]. }
assert (Z8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2120) 8 0).
{ memv HS 2%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia | reflexivity | lia]. }
(* YFh1.v:217-274: the unwinder's premises. *)
eapply SRr_bind.
{ apply (U1 W ly (ms_regs msU) (ms_mem msU) _ (sp0 - 2128) B_INTERCEPTOR_FREE_PC_OFF_138 sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; lia)), E2. unfold sp0. f_equal; lia. }
1:{ rreg HS (11%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (12%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; lia)), E2. unfold sp0. symmetry. apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (14%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity. }
1:{ lia. }
1:{ memv HS 3%nat 0%nat; [reflexivity | reflexivity | lia]. }
1:{ memv HS 7%nat 0%nat; [reflexivity | reflexivity | lia]. }
1:{ memv HS 8%nat 0%nat; [reflexivity | reflexivity | lia]. }
1:{ memv HS 28%nat 0%nat; [reflexivity | reflexivity | unfold TFIB_TSD; lia]. }
1:{ memv HS 29%nat 0%nat; [reflexivity | cbn [sv_denot]; rewrite (HEn1 33%nat ltac:(cbv; lia)), EaC; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia | clear - LB; numconst; lia]. }
1:{ memv HS 30%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 33%nat ltac:(cbv; lia)), EaC; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; lia); lia
| cbn [sv_denot]; rewrite (HEn1 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia | clear - LB; numconst; lia]. }
1:{ memv HS 31%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; lia); lia | reflexivity | lia]. }
1:{ memv HS 31%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; lia); lia
| cbn [sv_denot]; rewrite (HEn1 35%nat ltac:(cbv; lia)), EaTOP; unfold w64; rewrite Zbv_add_unsigned; f_equal; lia | clear - LB; numconst; lia]. }
1:{ memv HS 31%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; lia); lia
| cbn [sv_denot]; rewrite (HEn1 35%nat ltac:(cbv; lia)), EaTOP; unfold w64, ly_bot, kStackSpan; rewrite Zbv_add_unsigned; f_equal; lia
| unfold ly_bot, kStackSpan; clear - LB; numconst; lia]. }
1:{ memv HS 32%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; lia); unfold t_unwinding; lia | reflexivity | lia]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 32 _ _ HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; lia); numconst; lia | off_by ltac:(clear - LB; numconst; lia) ]. }
1:{ memv HS 23%nat 0%nat; [reflexivity | reflexivity | lia]. }
1:{ memv HS 24%nat 0%nat; [reflexivity | reflexivity | lia]. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; lia).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp_al. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; lia). clear - Hlo LB; numconst; lia. }
1:{ intros a Ha. rewrite Q2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - Usp Hlo LB; numconst; lia). apply PRES2. clear - Ha; numconst; lia. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by lia.
rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [lia | exact Hsp_al]. }
1:{ clear - Hlo LB; numconst; lia. }
1:{ right. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; lia). lia. }
1:{ intros a Ha. apply PRES2. clear - Ha; numconst; lia. }
1:{ clear; numconst; lia. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; lia). lia. }
1:{ exact Hbot. }
1:{ exact Hhi. }
1:{ apply (mod0_factor _ 8 2); [lia | exact Hsp_al]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 2%nat 9%nat;
[cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia | cbn [sv_denot]; rewrite (HEn1 1%nat ltac:(cbv; lia)), E1, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 2%nat 8%nat;
[cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia | cbn [sv_denot]; rewrite (HEn1 8%nat ltac:(cbv; lia)), E8, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ exact Hra4096. }
fold sp0 in Hch. destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hch].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [exact Hch|].
destruct Hch as [H16 Hfp]. split; [exact H16|].
apply Z.ltb_lt in Hf0.
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
eapply fpchain_ext2; [exact Hfp | lia |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|exact Hva]. intros i Hi. apply aview_same.
apply (proj1 MEQU (Z_to_bv 64 (a + i))); rewrite unsigned_lit_small by (clear - Ha1 Ha2 H16 Hi Usp LB; numconst; lia).
- apply WIN_not_high. lia.
- intros Hz. clear - Hz H16 Ha1 Hi LB Hlo. unfold IZONE in Hz. numconst. lia. }
(* YFh1.v:275-325: the unwinder's return, the frame trimmed to [-64, 0), the scratch window again. *)
clear Hle. intros W' c' Hle (-> & regs2 & mem2 & mat2 & -> & HP2 & Hfr2 & Hpr2 & Ht1 & Ht2 & Ht3). srr_norm_model.
rreg HS (1%bv : bv 5) Q1. rewrite Q1. clear Q1.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem msU x).
{ intros x Hx. rewrite Q2 in Hfr2. unfold w64, BST_SIZE in Hfr2. rewrite unsigned_lit_small in Hfr2 by (clear - Usp Hlo LB; numconst; lia).
apply Hfr2; clear - Hx; unfold ASTACK, UNW_STK in *; lia. }
(* the unwinder's raw frame: outside its window, the length word, the trace and the top-of-frame word *)
assert (Hfru : forall x : word, ~ (sp0 - 2128 - UNW_STK <= bv_unsigned x < sp0 - 2128) -> ~ (sp0 - 2120 <= bv_unsigned x < sp0 - 2116) ->
~ (sp0 - 2112 <= bv_unsigned x < sp0 - 2112 + 8 * 30) -> ~ (sp0 - 72 <= bv_unsigned x < sp0 - 64) -> mem2 x = ms_mem msU x).
{ intros x X1' X2' X3' X4'. rewrite Q2 in Hfr2. unfold w64, BST_SIZE in Hfr2. rewrite unsigned_lit_small in Hfr2 by (clear - Usp Hlo LB; numconst; lia).
apply Hfr2; clear - X1' X2' X3' X4'; lia. }
assert (OBJ0 : val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2128) 8 (sp0 - 2112)).
{ eapply val_mem_frame; [|exact OBJ0p]. intros k Hk. apply Hfru; rewrite unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; lia); clear - Hk; unfold UNW_STK; lia. }
assert (LEN : (1 <= length tr <= 30)%nat).
{ unfold YFgn.tr, call_trace. destruct (frame0_ok ly regs0); [apply unwind_of_chain_length | cbn; lia]. }
(* YFgc.v:230-242: the length word, its upper half kept at 0. *)
assert (OBJ1 : val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2120) 8 LENv).
{ unfold YFgn.LENv. replace (Z.of_nat (length tr)) with (Z.of_nat (length tr) + 2 ^ 32 * 0) by lia.
apply val_mem_4_4; [lia | lia | |].
- eapply val_mem_addr; [exact Ht1 | lia].
- assert (Z4 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msU)) (sp0 - 2120 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2120 + 4 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by lia.
rewrite (Z8 (4 + k)%nat ltac:(lia)). rewrite !le_byte_zero. reflexivity. }
eapply val_mem_frame; [|exact Z4]. intros k Hk. apply Hfru; rewrite unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; lia); clear - Hk; unfold UNW_STK; lia. }
assert (TRA2 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem2) (sp0 - 2112 + 8 * Z.of_nat i) 8 (nth i tr 0)).
{ intros i Hi. eapply val_mem_addr; [apply Ht2; exact Hi | lia]. }
clear Ht1 Ht2 Ht3.
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?rim :: ?rscr :: ?rfr :: ?rest =>
pose proof (st_ok_after_call tfibsegs 70 En1 ss ms0 regs2 (mrestrict (w_H W) mem2) (rim :: trim_lo rfr (-64) :: rest) B_INTERCEPTOR_FREE_PC_OFF_194 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_drop; apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP2) as HS1;
let rsv := eval vm_compute in (rim :: trim_lo rfr (-64) :: rest) in
change (rim :: trim_lo rfr (-64) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv 70 B_INTERCEPTOR_FREE_PC_OFF_194) in
change (ss_after_call ss rsv 70 B_INTERCEPTOR_FREE_PC_OFF_194) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?r1 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs En1 (mrestrict (w_H W) (ms_mem msU)) (mrestrict (w_H W) mem2)) (r0 :: r1 :: tail));
[ constructor; [|constructor];
[ eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn1 37%nat ltac:(cbv; lia)), EaIM; unfold w64; rewrite unsigned_lit_small by (clear - IMR; numconst; lia); intros a Ha; cbn beta; clear - Ha IMR Hlo LB Usp; numconst; lia
| eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite (HEn1 2%nat ltac:(cbv; lia)), E2; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; lia
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with YFgn.SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts En1 r HEn1 Hr) as (Y1 & Y2 & Y3 & Y4 & Y5);
eapply (kept_of_frame En1 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr' Hpr2); intros a Ha; cbn beta; clear - Ha Y1 Y2 Y3 Y4; numconst; lia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES3 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem2 a) by (intros a Ha; apply Hpr2, PRES2, Ha).
set (En2 := havoc En1 70 (map (getr regs2) CLOB)) in HS1.
assert (HEn2 : forall k, (k < aHAVf)%nat -> ew En2 k = ew E0 k) by (intros k Hk; subst En2; unfold aHAVf in Hk; rewrite ew_havoc_old by lia; apply HEn1; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; unfold IFRAME;
split; [clear - Usp Hlo LB; numconst; lia|]; split; [clear - Usp Hlo LB; numconst; lia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Usp Hlo LB Ho; numconst; lia) | apply PRES3; clear - Ho; numconst; lia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|[<-|Hr']];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 37%nat ltac:(cbv; lia)), (HEn2 2%nat ltac:(cbv; lia)), EaIM, E2;
unfold w64; rewrite unsigned_lit_small by (clear - IMR; numconst; lia); clear - IMR Usp Hlo LB; numconst; lia
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; lia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with YFgn.SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En2 r' HEn2 Hr') as (Y1 & Y2 & Y3 & Y4 & Y5);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; lia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. clear HS. rename HS1 into HS.
assert (MEQ2 : MEQI mem2).
{ destruct MEQU as [M I]. assert (LOWEQ : forall a, a < sp0 - ASTACK -> 0 <= a -> mem2 (Z_to_bv 64 a) = ms_mem msU (Z_to_bv 64 a)).
{ intros a Ha Ha'. apply Hfr'. rewrite unsigned_lit_small by (clear - Ha Ha' Usp; unfold ASTACK in *; lia). lia. }
split.
- intros x Hx Hz. rewrite <- (M x Hx Hz). apply Hfr'. intros HH. apply Hx. left. unfold ASTACK in *. lia.
- destruct I as (I1 & I2 & I3 & I4 & I5). unfold IAL_POST.
repeat match goal with |- _ /\ _ => split end;
try (eapply val_mem_frame; [|eassumption]; intros k Hk; apply LOWEQ; clear - Hk Hlo LB; numconst; lia).
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msU) mem2 a) by (apply LOWEQ; clear - Ha Hlo LB; numconst; lia). apply I5. exact Ha. }
clear MEQU.
(* YFgc.v:191 segB's first run: +0x194 through asan_free, stopped at Deallocate's entry. *)
srr_run_to_sh tfibtbl_rtF_ok HS tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En2 _ _ HS eq_refl) as HshA; cbn [ss_pc] in HshA.
lazymatch type of HF with frame_of _ ?rs _ _ =>
pose proof (MEQI_frame En2 rs _ _ HEn2 ltac:(vm_compute; reflexivity) HF MEQ2) as MEQA end.
(* the run's windows (YFh1.v:340-349): the scratch window below the frame, the frame's top [-64, 0), T + t_unwinding *)
assert (FRR : forall y : word, ~ (sp0 - ASTACK <= bv_unsigned y < sp0 - IFRAME) -> ~ (sp0 - 64 <= bv_unsigned y < sp0) ->
~ (T + t_unwinding <= bv_unsigned y < T + t_unwinding + 1) -> ms_mem msA y = mem2 y).
{ intros y Y1 Y2 Y3. apply HF. intros Hw. destruct (in_wrange_windows En2 _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hr;
rewrite ?(HEn2 2%nat ltac:(cbv; lia)), ?E2, ?(HEn2 32%nat ltac:(cbv; lia)), ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by (clear - LB; numconst; lia);
clear - Y1 Y2 Y3 Hr; unfold IFRAME, ASTACK, t_unwinding in *; unfold sp0, T in *; lia |]).
destruct Hin. }
clear HF.
pose proof stack_ivs as (IT & _).
assert (NT : forall a, sp0 - ASTACK <= a < sp0 -> ~ (T + t_unwinding <= a < T + t_unwinding + 1)).
{ intros a Ha Ht. clear - Ha Ht IT. unfold kThreadObjSize, t_unwinding, ASTACK in *. lia. }
assert (FRM : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ms_mem msA (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
{ intros a Ha. apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; lia);
[clear - Ha; unfold IFRAME, ASTACK in *; lia | clear - Ha; lia | apply NT; clear - Ha; unfold IFRAME, ASTACK in *; lia]. }
apply SRr_ret. unfold at_DEALLOC. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg _ (with_vm_backing _ ?mt _) = _ /\ _ => exists (ms_regs msA), (ms_mem msA), mt end.
split. { rewrite HshA at 1. reflexivity. }
split. { rreg HS (1%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (2%bv : bv 5) R; rewrite R, (HEn2 2%nat ltac:(cbv; lia)), E2. unfold w64, sp0. f_equal; lia. }
split. { rreg HS (10%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (11%bv : bv 5) R; rewrite R, (HEn2 10%nat ltac:(cbv; lia)). apply Er. reflexivity. }
split. { rreg HS (12%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (13%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (14%bv : bv 5) R; rewrite R, (HEn2 2%nat ltac:(cbv; lia)), E2. unfold w64, sp0. f_equal; lia. }
split. { rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (8%bv : bv 5) R; rewrite R, (HEn2 2%nat ltac:(cbv; lia)). apply Er. reflexivity. }
split. { rreg HS (3%bv : bv 5) R; rewrite R, (HEn2 3%nat ltac:(cbv; lia)). apply Er. reflexivity. }
split. { rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
split. { intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
repeat match type of Hr' with _ \/ _ => destruct Hr' as [Hr'|Hr'] end; subst r;
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
let kb := eval vm_compute in (Z_to_bv 5 k : bv 5) in
let RR := fresh "RR" in rreg HS kb RR; change (Z_to_bv 5 k) with kb; rewrite RR, HEn2 by (cbv; lia); apply Er; reflexivity end. }
split; [exact MEQA|].
split. { memv HS 32%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 32%nat ltac:(cbv; lia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; lia); unfold t_unwinding; lia | reflexivity | lia]. }
split. { intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)) as [A1|A1]; [|destruct (Z_lt_le_dec a (sp0 - 64)) as [A2|A2]].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; clear - Ha A1; numconst; unfold sp0 in *; lia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; lia) ].
- apply (apresent_same (w_H W) mem2); [|apply PRES3; exact Ha].
apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; lia);
[clear - A1; unfold IFRAME, ASTACK in *; lia | clear - A2; lia | exact (NT a Ha)].
- eapply (st_ok_window_apresent_off (w_H W) En2 _ _ 2 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; clear - Ha A2; numconst; unfold sp0 in *; lia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; lia) ]. }
split. { eapply val_mem_frame; [|exact OBJ0]. intros k Hk. apply FRM. unfold IFRAME. lia. }
split. { eapply val_mem_frame; [|exact OBJ1]. intros k Hk. apply FRM. unfold IFRAME. lia. }
split. { intros i Hi. eapply val_mem_frame; [|exact (TRA2 i Hi)].
intros k Hk. apply FRM. unfold IFRAME. clear - Hi Hk LEN. lia. }
split. { memv HS 2%nat 6%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia
| cbn [sv_denot]; rewrite (HEn2 1%nat ltac:(cbv; lia)), E1, Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 5%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia
| cbn [sv_denot]; rewrite (HEn2 8%nat ltac:(cbv; lia)), E8, Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 4%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia
| cbn [sv_denot]; rewrite (HEn2 9%nat ltac:(cbv; lia)), (Er 9 9%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia
| cbn [sv_denot]; rewrite (HEn2 18%nat ltac:(cbv; lia)), (Er 18 18%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia
| cbn [sv_denot]; rewrite (HEn2 19%nat ltac:(cbv; lia)), (Er 19 19%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 2%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia
| cbn [sv_denot]; rewrite (HEn2 20%nat ltac:(cbv; lia)), (Er 20 20%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
memv HS 2%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn2 2%nat ltac:(cbv; lia)), E2; unfold sp0; lia
| cbn [sv_denot]; rewrite (HEn2 21%nat ltac:(cbv; lia)), (Er 21 21%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range].
Qed.
End WK.
End c.
