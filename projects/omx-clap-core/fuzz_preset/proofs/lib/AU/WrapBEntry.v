(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025): the facts
   an interceptor walk over ARcf reads at its entry, shared by the malloc walk (WrapMallocBCall.v) and the free walk.
   From acall_pre_cf (YG0dcf.v:221-250) and TfibSyms B alone: the entry registers, stack bounds and frame chain; the
   layout zones (YFgn.v:125-200 LYB / LYD / stack_ivs, cgif's ARm site file, restated over layout_ok and img_cover);
   at an environment E0 whose atoms 2, 32, 33 are sp, T and C (the seed environments of YFgn.v:41-43 / WrapMallocBSeed.v):
   the seed's writable windows (YFgn.v:201-265) and the zones of YFgn.SKEL_TAIL's regions (YFgn.v:337-386, without
   the internal allocator's zone). No instruction is read here. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import WrapBKit.
Import ListNotations.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section WK.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)).
Hypothesis PRE : acall_pre_cf tfibsegs B ly S Hp W regs0 mem0 md0 ch.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
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

Section ENV.
Variable E0 : env.
Hypothesis E2 : ew E0 2 = getr regs0 2.
Hypothesis EaT : ew E0 32 = w64 T.
Hypothesis EaC : ew E0 33 = w64 (ly_C ly).
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

(* YFgn.v:337-386 SKEL_TAIL / tail_facts, without the internal allocator's zone (the malloc walk has no
   internal-allocator call). *)
Definition RFACTS (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - ASTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFIB_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFIB_IMG_LO)).
Lemma zone_lit : forall lo hi wlo whi, TFIB_IMG_LO <= lo -> hi <= TFIB_IMG_END -> whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz5.
pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & T3 & T4 & T5). pose proof Hsp as (S1 & S2 & S3).
unfold RFACTS; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. clear - Hz0 Hz1 Hz5 T1 T5 S1. numconst. unfold sp0 in *. lia.
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
(YP09.r_whi r <= YP09.r_wlo r \/ (TFIB_IMG_END <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= 2 ^ 64) \/ (0 <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= TFIB_IMG_LO)).
Proof.
intros E r HE Hin. pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & LB).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
let sk := eval vm_compute in YFgn.SKEL_TAIL in change YFgn.SKEL_TAIL with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (clear - HE; cbv; lia); rewrite ?E2, ?EaT, ?EaC; unfold w64;
rewrite ?unsigned_lit_small by (clear - F1 F7; numconst; unfold T in *; lia).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D))
by (clear - RF; destruct RF as (X1 & X2 & X3 & X4); refine (conj X1 (conj X2 (conj X3 _))); clear - X4; unfold zone3, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia) end.
all: first [ apply zone_lit; clear; numconst; unfold TFIB_TSD, TFIB_TP; lia
| apply zone_T; clear - F1 F2; numconst; unfold T in *; lia
| apply zone_C; clear - F7 F8; numconst; lia ].
Qed.

End ENV.
End WK.
End c.
