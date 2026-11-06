(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025), the
   SEED of the FREE interceptor walk over ARcf: the symbolic state at __wrap_free's first instruction
   (B 0x53820, YImgCellsB.B_WRAP_FREE_PC) from acall_pre_cf (YG0dcf.v:221-250), TfibSyms B and the pointer's range
   (a0 < 2 ^ 47, which every free argument meets: PNull is 0 and a live block lies below ASAN_CEIL,
   YGcfBlockRange.block_user_range_cf).
   Ported BY STATEMENT from YFg3.v:110-249 (cgif's free-NULL site, its seed of YFgn.SS0 from acall_pre over ARm),
   in the cf form of lib/AU/WrapMallocBSeed.v (the malloc walk's seed):
   - the region list and the facts are YFgn.REG0 / YFgn.FFN (YFgn.v:60-85) unchanged;
   - the environment XWf is YFgn.XW (YFgn.v:41-42; free's trace, call_trace at B_INTERCEPTOR_FREE_PC_OFF_138) with
     atom 37 (aIM) the internal allocator's map slot of the pointer, IMf p = YFgi.IMv p (YFgi.v:42), in place of the
     slot of 0 (YFgn's a0 = 0 arm): the walk is one script for PNull and for a block;
   - SS0f is YFgn.SS0 (YFgn.v:86) without the a0 = 0 pin;
   - the proofs read ARmcf / ALedger_cf through WrapBKit.v (cf_const_lookup, cf_const_lookup_sym, cf_cell_state,
     HIGH_cf, SX_cf, img_cover_of_ledger_cf).
   Reads the runtime decode table only through the region list (no instruction is stepped here). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFeq YFex YFfy YFfu YFgn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import WrapBKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* YFgn.v:39-43 with aIM the pointer's map slot (YFgi.v:42). *)
Definition IMf (p : Z) : Z := B_INTERNAL_ALLOC_PLACEHOLDER_CELL + 8 * (p / 2 ^ 32).
Definition XWf (ly : alayout) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : list word :=
[ w64 (ly_T ly); w64 (ly_C ly); w64 (ly_space ly); w64 (ly_top ly); w64 (YFgn.LENv ly regs ch);
  w64 (IMf (bv_unsigned (getr regs 10))); w64 0; w64 0; w64 SHADOW_OFF ].
Definition E0f (ly : alayout) (regs : bvmap 5 word) (ch : list (Z * Z * Z)) : env := Ereg regs (XWf ly regs ch).
(* YFgn.v:86, tp pinned only. *)
Definition SS0f : sstate := mkSS B_WRAP_FREE_PC (sr_set sr_atoms 4%bv (SLit TFIB_TP)) YFgn.REG0 None YFgn.FFN.

Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (ch : list (Z * Z * Z)).
Let sp0 : Z := bv_unsigned (getr regs 2).
Hypothesis PRE : acall_pre_cf tfibsegs B ly S Hp W regs mem md ch.
(* the pointer is below 2 ^ 47 (the high-bits test at ___interceptor_free + 0x34 falls through) *)
Hypothesis HP47 : bv_unsigned (getr regs 10) < 2 ^ 47.
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation E0 := (E0f ly regs ch).
Local Notation LENv := (YFgn.LENv ly regs ch).
Lemma Mcf : ARmcf B ly S Hp rd0. Proof. exact (proj1 (proj1 PRE)). Qed.
Lemma LO : layout_ok ly. Proof. exact (cf_layout B ly S Hp _ _ Mcf). Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite (amc_tsd _ _ _ _ _ Mcf). exact (ts_tsd B TB). Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. exact (cf_const_lookup_sym B TB ly S Hp H0 mem Mcf e w e' E). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. intros a w x E. exact (cf_const_lookup B TB ly S Hp H0 mem Mcf a w x E). Qed.
Lemma unwinding_val : val_mem tfibsegs m0 (T + t_unwinding) 1 0.
Proof. exact (cf_unwinding_val B ly S Hp H0 mem Mcf). Qed.
Lemma HSP : ly_stk_lo ly + ASTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & Hlo & _ & Hhi & _). unfold spZ in *. unfold sp0. lia. Qed.
Lemma IMG : img_cover ly.
Proof. destruct PRE as ((_ & LED & _) & _). exact (img_cover_of_ledger_cf ly S md LED). Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) kPtrArrayResv /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) kFakeStackSize /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_stk_lo ly mod 4096 = 0.
Proof. exact (HIGH_cf ly LO IMG). Qed.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs r.
Proof. intros Hk. exact (ew_Ereg_nat regs (XWf ly regs ch) k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. reflexivity. Qed.
Lemma EaIM : ew E0 37 = w64 (IMf (bv_unsigned (getr regs 10))). Proof. reflexivity. Qed.
Lemma EaSHB : ew E0 40 = w64 SHADOW_OFF. Proof. reflexivity. Qed.
(* YFg3.v:118-132. *)
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k d))).
Proof.
intros base a w k d x Hk Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfibsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfibsegs m0 o.
Proof. intros a w v o Hv Ho Ha. apply vis_writable_off; [exact Ha|]. replace o with (a + (o - a)) by lia. eapply val_mem_vis; [exact Hv | lia]. Qed.
Ltac offw := first [ lia | apply off_img_high; unfold TFIB_IMG_END, kHighMemBeg, YImgTop.IMG_TOP_B in *; ceil; unfold ASAN_CEIL in *; lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HI)))))); unfold kThreadObjSize, t_qc, t_unwinding, t_stats, t_cache in *; lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac lit_region :=
reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
(* YFg3.v:140-187. *)
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) YFgn.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kHighShadowBeg in hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, S1, S2, T2, T4, T7.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
destruct PRE as (_ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
unfold YFgn.REG0, flit1, flit4, flit8, flits8, fatom8; unfold B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_30_CELL, B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_48_CELL, B_ASAN_INITED_CELL, B_ASAN_SHADOW_MEMORY_DYNAMIC_ADDRESS_CELL, B_CAN_POISON_MEMORY_CELL, B_COMMON_FLAGS_DONT_USE_OFF_20_CELL, B_GOT_0X40, B_GOT_0X50, B_GOT_0X58, B_GOT_0X60, B_GOT_0X68, B_GOT_0X70, B_GOT_0X78, B_GOT_0X80, B_GOT_OFF_40_VAL, B_GOT_OFF_50_VAL, B_GOT_OFF_58_VAL, B_GOT_OFF_60_VAL, B_GOT_OFF_68_VAL, B_GOT_OFF_70_VAL, B_GOT_OFF_78_VAL, B_GOT_OFF_80_VAL, B_INSTANCE_OFF_318_CELL, B_INSTANCE_OFF_328_CELL, B_KHIGHMEMEND_CELL, B_KMIDMEMBEG_CELL, B_KMIDMEMEND_CELL, B_MALLOC_CONTEXT_SIZE_CELL, B_MEMSET_PC, B_MFHOOKS_OFF_8_CELL, B_PAGESIZECACHED_CELL, B_REAL_MEMSET_CELL, B_TSD_KEY_CELL, B_TSD_KEY_INITED_CELL in *. cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- ASTACK)); [rewrite E2; reflexivity | unfold ASTACK in *; lia | lia |].
intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, ASTACK, YImgTop.IMG_TOP_B in *; lia | apply HPRES; exact Ha]. }
do 11 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 40%nat 0 SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; lia | | unfold SHADOW_OFF; cbn; lia | cbn; lia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 13 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; lia | cbn; lia].
fold B_BUILTIN_TLS_OFF_C8_CELL; replace (B_BUILTIN_TLS_OFF_C8_CELL - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TB); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. unfold TFIB_TSD. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
rewrite Z.add_0_l. fold B_PTHREAD_TSD_MAIN_CELL; replace B_PTHREAD_TSD_MAIN_CELL with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite EaT; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; lia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [rewrite EaTOP; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; lia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [rewrite EaTOP; unfold w64; f_equal; lia | unfold kStackSpan; lia | | unfold kStackSpan; cbn; lia | cbn; lia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; lia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity.
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; lia). apply (cell_sym (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
apply Forall_cons; [|apply Forall_nil]. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_unwinding.
pose proof unwinding_val as U. unfold t_unwinding in U.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ U); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; unfold YImgTop.IMG_TOP_B in *; offw. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [exact U | cbn; lia | cbn; lia]. }
Qed.
(* YFg3.v:188-213. *)
Lemma PAIRS_ok : pairwise_disjoint E0 YFgn.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
pose proof HSP as [S1 S2].
pose proof (SX_cf ly LO 2 6 _ _ eq_refl eq_refl ltac:(lia)) as DCT.
pose proof (SX_cf ly LO 6 8 _ _ eq_refl eq_refl ltac:(lia)) as DCS.
pose proof (SX_cf ly LO 2 8 _ _ eq_refl eq_refl ltac:(lia)) as DTS.
unfold zdisjoint in DCT, DCS, DTS. cbn [fst snd] in DCT, DCS, DTS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply pairwise_disjoint_of_extents. unfold YFgn.REG0, flit1, flit4, flit8, flits8, fatom8, extent_of_region; unfold B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_30_CELL, B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_48_CELL, B_ASAN_INITED_CELL, B_ASAN_SHADOW_MEMORY_DYNAMIC_ADDRESS_CELL, B_CAN_POISON_MEMORY_CELL, B_COMMON_FLAGS_DONT_USE_OFF_20_CELL, B_GOT_0X40, B_GOT_0X50, B_GOT_0X58, B_GOT_0X60, B_GOT_0X68, B_GOT_0X70, B_GOT_0X78, B_GOT_0X80, B_GOT_OFF_40_VAL, B_GOT_OFF_50_VAL, B_GOT_OFF_58_VAL, B_GOT_OFF_60_VAL, B_GOT_OFF_68_VAL, B_GOT_OFF_70_VAL, B_GOT_OFF_78_VAL, B_GOT_OFF_80_VAL, B_INSTANCE_OFF_318_CELL, B_INSTANCE_OFF_328_CELL, B_KHIGHMEMEND_CELL, B_KMIDMEMBEG_CELL, B_KMIDMEMEND_CELL, B_MALLOC_CONTEXT_SIZE_CELL, B_MEMSET_PC, B_MFHOOKS_OFF_8_CELL, B_PAGESIZECACHED_CELL, B_REAL_MEMSET_CELL, B_TSD_KEY_CELL, B_TSD_KEY_INITED_CELL in *.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP.
rewrite E2, EaT, EaC. unfold w64.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, ASTACK in *.
fold sp0. rewrite !unsigned_lit_small by lia.
clear - S1 S2 hT1 hT2 hC1 hC2 hS1 hS2 hSP1 hSP2 hP1 hP2 Usp DCT DCS DTS CR CR0.
unfold TFIB_TP, TFIB_TSD, t_unwinding in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in hT1, hC1; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
repeat split;
first [ clear DCT DCS DTS hT1 hC1; lia
| clear - hT1 CR0; lia
| clear - hC1 CR0; lia
| clear - hC1 hC2 hT1 hT2 DCT; lia
| clear - hC1 hC2 S1 S2 hS1 hS2 Usp DCS; lia
| clear - hT1 hT2 S1 S2 hS1 hS2 Usp DTS; lia ].
Qed.
(* YFg3.v:214-239, aIM at the pointer's slot. *)
Lemma FACTS_ok : atoms_ok E0 (f_atoms YFgn.FFN).
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct PRE as (_ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. pose proof (lo_C_al ly LO) as CAL. unfold page_aligned in TAL, T3.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kHighShadowBeg, ASTACK in
hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, S1, S2, T2, T4, T7.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (HL : 1 <= LENv <= 30).
{ unfold YFgn.LENv, YFgn.tr, call_trace, frame0_ok, spZ, raZ, s0Z. fold sp0.
pose proof (unwind_of_chain_length B_INTERCEPTOR_FREE_PC_OFF_138 ((sp0, bv_unsigned (getr regs 1), bv_unsigned (getr regs 8)) :: ch)) as LEN.
destruct (sp0 + 16 <? ly_top ly); cbn [length]; lia. }
assert (HPA : 0 <= bv_unsigned (getr regs 10) < 2 ^ 47) by (split; [apply u64_range | exact HP47]).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
cbn [YFgn.FFN f_atoms atoms_ok]. unfold aSB, aSHB, aC, aT, aTOP, aLEN, aIM.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 T4 Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat T); [exact EaT| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact EaC| | | |]. all: clear - CR0 hC1 hC2 CAL; first [lia | exact CAL]. }
split. { apply (AF 34%nat SB); [exact EaSB| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact EaTOP| | | |]. all: clear - CR0 T1 T2 T3 T4 T7 hS1; unfold ly_bot, kStackSpan in *; first [lia | exact T3]. }
split. { apply (AF 36%nat LENv); [exact EaLEN| | | |]. all: clear - CR0 HL; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat (IMf (bv_unsigned (getr regs 10)))); [exact EaIM| | | |]. all: clear - HPA; unfold IMf, B_INTERNAL_ALLOC_PLACEHOLDER_CELL; first [lia | change (2 ^ 3) with 8; lia]. }
split; [|exact I]. { apply (AF 40%nat SHADOW_OFF); [exact EaSHB| | | |]. all: clear; unfold SHADOW_OFF; first [lia | reflexivity]. }
Qed.
(* YFg3.v:240-249, at __wrap_free with tp pinned only (a0 is the pointer, not pinned). *)
Lemma SEED_ok : st_ok tfibsegs E0 SS0f (restrict (w_H W) (mkst regs (w64 B_WRAP_FREE_PC) mem (seg_rom tfibsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
rewrite restrict_mkst_fx. unfold SS0f, E0f, w64; unfold B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_30_CELL, B_ASAN_FLAGS_DONT_USE_DIRECTLY_OFF_48_CELL, B_ASAN_INITED_CELL, B_ASAN_SHADOW_MEMORY_DYNAMIC_ADDRESS_CELL, B_CAN_POISON_MEMORY_CELL, B_COMMON_FLAGS_DONT_USE_OFF_20_CELL, B_GOT_0X40, B_GOT_0X50, B_GOT_0X58, B_GOT_0X60, B_GOT_0X68, B_GOT_0X70, B_GOT_0X78, B_GOT_0X80, B_GOT_OFF_40_VAL, B_GOT_OFF_50_VAL, B_GOT_OFF_58_VAL, B_GOT_OFF_60_VAL, B_GOT_OFF_68_VAL, B_GOT_OFF_70_VAL, B_GOT_OFF_78_VAL, B_GOT_OFF_80_VAL, B_INSTANCE_OFF_318_CELL, B_INSTANCE_OFF_328_CELL, B_KHIGHMEMEND_CELL, B_KMIDMEMBEG_CELL, B_KMIDMEMEND_CELL, B_MALLOC_CONTEXT_SIZE_CELL, B_MEMSET_PC, B_MFHOOKS_OFF_8_CELL, B_PAGESIZECACHED_CELL, B_REAL_MEMSET_CELL, B_TSD_KEY_CELL, B_TSD_KEY_INITED_CELL, B_WRAP_FREE_PC, B_INTERCEPTOR_FREE_PC_OFF_138 in *. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact Htp].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.
End f.
End b.
