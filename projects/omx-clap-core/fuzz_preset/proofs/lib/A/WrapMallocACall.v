(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image A (asan, pin 1be0f53d96cb, unstripped twin bff8519bbe3e;
   relocated from d83eb25d by symbol + offset, the internal file RELOC102-A1.md), the
   CALL SEGMENT of the malloc interceptor over ARcf: __wrap_malloc's entry (A 0x53738 `j ___interceptor_malloc`,
   pc_wrap_malloc Tfib_code) to Allocate's entry (CfImg's cf_pc_allocate, A 0x325b8 = AB1w.v:52
   tfib_A__ZN6__asan9Allocator8Allocate...), through ___interceptor_malloc (0x53910; TryAsanInitFromRtl,
   GetMallocContextSize, GetCurrentPc, the BufferedStackTrace set-up, UnwindImpl) and asan_malloc (0x3255c) up to its
   `jal Allocate` (0x32584). The image-A twin of a Theorem Labs lane's lib/AU/WrapMallocBCall.v (same proof, A's names).
   Code read: the runtime decode table AB1q.tfibtbl_rtA (lib/A/AB1q.v at the base: build_table over tfibsegs, the
   loaded segments of the image the proof loads, at 0x53734 (206 instructions), 0x53910.., 0x3255c.., 0x5b4c4..).
   Ported BY STATEMENT from the image-A donors over cgif's ARm (relocated to this image):
   - the prefix to UnwindImpl and its return: lib/A/AFjh.v:458-613 seg0 (in the released file, deleted in this series; srr_run_to_sh to UnwindImpl, A 0x5b4d4 =
     AB1w.v:421, the unwinder's spec, the stack object's regions); its U1 premises at the free donor's region list as
     lib/A/AFh1.v:218-275 states them (the seed here is AFgn.REG0, WrapMallocASeed.v);
   - asan_malloc to Allocate's entry: the first run of lib/A/AGji.v:401 seg1 (s_runP from S_1 through asan_malloc
     into Allocate), stopped at Allocate's entry;
   - UnwindImpl is the donors' named premise U1 : tfib_unwind_spec (AFl0.v:23-57), relation-generic, taken as is
     (a Theorem Labs lane: discharged by A's tfib_unwind_ok, AFl0.v).
   The dlsym arm (TryAsanInitFromRtl returns 0) and the short-context arm (GetMallocContextSize <= 2) are refuted as
   the donor refutes them: asan_inited (0xabb98) reads 1 and malloc_context_size (0xabbbc, AF0m.v:87) reads 30 in
   the seed (Tfib_const through ARmcf's amc_const), so the symbolic run takes neither branch.
   The two return addresses the segment leaves (RA_ALLOC, RA_ASAN_MALLOC below) are named from AB1w's entries. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq AFgn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import WrapAKit WrapMallocASeed.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Export WrapMallocAConsts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
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
Hypothesis U1 : tfib_unwind_spec.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let m0 := mrestrict (w_H W) mem0.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (pc_wrap_malloc Tfib_code)) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Local Notation E0 := (E0m ly regs0 ch).
Local Notation LENv := (LENm ly regs0 ch).
Local Notation tr := (trm ly regs0 ch).

(* The entry facts, from acall_pre_cf (YG0dcf.v:48-71) and TfibSyms. *)
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
Proof. intros Hk. exact (ew_Ereg_nat regs0 (XWm ly regs0 ch) k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. exact (Er 8 8%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = getr regs0 10. Proof. exact (Er 10 10%bv eq_refl). Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. reflexivity. Qed.

(* AFgn.v:125-149 LYB, :167-184 LYD, :185-200 iv_vs_stack / stack_ivs, from layout_ok and img_cover alone. *)
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
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
split; [clear - IP; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|]. split; [clear - HSP; lia|]. split; [clear - HSP; lia|]. split; [clear - IP; lia|].
split; [exact ZC|]. split; [clear - ZC; unfold zone3 in ZC; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
split; [exact ZNB|]. split; [clear - ZNB; unfold zone3 in ZNB; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
split; [exact ZSB|]. split; [clear - ZSB; unfold zone3 in ZSB; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
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

(* AFgn.v:201-265: the seed's writable windows (the stack window and T + t_unwinding). *)
Definition WIN (a : Z) : Prop := (sp0 - ASTACK <= a < sp0) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Lemma WSKEL_WIN : forall (E : env) a t,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> In t AFgn.WSKEL ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN a.
Proof.
intros E a t HE Hin Hr. pose proof LYB as HF.
unfold AFgn.WSKEL in Hin. cbn [In] in Hin. unfold WIN.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, aHAVf, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by (cbv; lia);
rewrite ?E2, ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0, T in *; lia.
Qed.
Lemma windows_WIN : forall (E : env) rs a,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (AFgn.win_sub t) AFgn.WSKEL || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub).
assert (SUB : forall E' a' t u', AFgn.win_sub t u' = true ->
base_val E' (fst (fst t)) + snd (fst t) <= a' < base_val E' (fst (fst t)) + snd t ->
base_val E' (fst (fst u')) + snd (fst u') <= a' < base_val E' (fst (fst u')) + snd u').
{ clear. intros E' a' [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold AFgn.win_sub in Hs. cbn [fst snd] in *.
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
- clear - Hs S1 S2 S3 HF. ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
- clear - Ht F1. ceil; unfold zone3, zone3cases, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. unfold T in *. lia.
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
| unfold off_img; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; unfold TFIB_IMG_LO; unfold YImgTop.IMG_LO in *; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; tac ].

(* AFgn.v:337-386 SKEL_TAIL / tail_facts, without the internal allocator's zone (the malloc walk has no
   internal-allocator call). *)
Definition RFACTS (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - ASTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFIB_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFIB_IMG_LO)).
Lemma zone_lit : forall lo hi wlo whi, TFIB_IMG_LO <= lo -> hi <= TFIB_IMG_END -> whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz5.
pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & T3 & T4 & T5). pose proof Hsp as (S1 & S2 & S3).
unfold RFACTS; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. clear - Hz0 Hz1 Hz5 T1 T5 S1. numconst. unfold sp0 in *. lia.
Qed.
Lemma zone_T : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof LYB as (F1 & _).
pose proof stack_ivs as (IT & _).
unfold RFACTS; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. clear - Hz0 Hz1 Hz2 F1 IT. numconst. unfold T, sp0 in *. lia.
Qed.
Lemma zone_C : forall lo hi wlo whi,
ly_C ly <= lo -> hi <= ly_C ly + 256 -> (whi <= wlo \/ (ly_C ly <= wlo /\ whi <= ly_C ly + 256)) -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof LYB as (_ & _ & _ & _ & _ & _ & F7 & _).
pose proof stack_ivs as (_ & _ & IC & _).
unfold RFACTS; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. clear - Hz0 Hz1 Hz2 F7 IC. numconst. unfold sp0 in *. lia.
Qed.
Lemma tail_facts : forall (E : env) r,
(forall k, (k < aHAVf)%nat -> ew E k = ew E0 k) -> In (skel r) AFgn.SKEL_TAIL ->
let b := base_val E (YP09.r_base r) in
(b + YP09.r_hi r <= sp0 - ASTACK \/ sp0 <= b + YP09.r_lo r) /\ 0 <= b + YP09.r_lo r /\ b + YP09.r_hi r <= 2 ^ 64 /\
(YP09.r_whi r <= YP09.r_wlo r \/ (TFIB_IMG_END <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= 2 ^ 64) \/ (0 <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= TFIB_IMG_LO)).
Proof.
intros E r HE Hin. pose proof LYB as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & LB).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
let sk := eval vm_compute in AFgn.SKEL_TAIL in change AFgn.SKEL_TAIL with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (clear - HE; cbv; lia); rewrite ?E2, ?EaT, ?EaC; unfold w64;
rewrite ?unsigned_lit_small by (clear - F1 F7; numconst; unfold T in *; lia).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D))
by (clear - RF; destruct RF as (X1 & X2 & X3 & X4); refine (conj X1 (conj X2 (conj X3 _))); clear - X4; unfold zone3, kLowShadowBeg, TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia) end.
all: first [ apply zone_lit; clear; numconst; unfold TFIB_TSD, TFIB_TP; lia
| apply zone_T; clear - F1 F2; numconst; unfold T in *; lia
| apply zone_C; clear - F7 F8; numconst; lia ].
Qed.

(* The state at Allocate's entry: registers (asan_malloc's call Allocate(&instance, n, 8, &stack, FROM_MALLOC,
   can_fill)), the interceptor's and asan_malloc's saved registers, the stack object and its trace, and the frame of
   the whole segment (memory changed only in the caller's stack window and T + t_unwinding, which reads 0 again). *)
Definition at_ALLOC (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regsA memA mat,
c' = mkCfg (mkst regsA (w64 PC_ALLOCATE) memA (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regsA 1 = w64 RA_ALLOC /\ getr regsA 2 = w64 (sp0 - 2144) /\
getr regsA 10 = w64 TFIB_INST /\ getr regsA 11 = getr regs0 10 /\ getr regsA 12 = w64 8 /\
getr regsA 13 = w64 (sp0 - 2128) /\ getr regsA 14 = w64 1 /\ getr regsA 15 = w64 1 /\
getr regsA 8 = getr regs0 2 /\ getr regsA 9 = getr regs0 10 /\ getr regsA 3 = getr regs0 3 /\ getr regsA 4 = w64 TFIB_TP /\
(forall r : Z, 22 <= r <= 27 -> getr regsA (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) /\
(forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> ~ (T + t_unwinding <= bv_unsigned x < T + t_unwinding + 1) -> memA x = mem0 x) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (T + t_unwinding) 1 0 /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) memA a) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2128) 8 (sp0 - 2112) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2120) 8 LENv /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2112 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 56) 8 (bv_unsigned (getr regs0 21)) /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2144) 8 sp0 /\
val_mem tfibsegs (mrestrict (w_H W) memA) (sp0 - 2136) 8 RA_ASAN_MALLOC.

Lemma seg_call : SRr tfibsegs W cfg0 at_ALLOC.
Proof.
pose proof Hwx_tfa as Hwx. pose proof (SEED_ok B TB ly S Hp W regs0 mem0 md0 ch PRE) as HS.
pose proof Hsp as (Hlo & Hbot & Hhi). pose proof LYB as LB. pose proof LY as LY. pose proof IMG as IMG.
pose proof Hal as Hsp_al. pose proof Hch as Hch. pose proof Hra4096 as Hra4096.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
(* AFjh.v:463 (in the released file lib/A/AFjh.v, deleted in this series), the run to the unwinder. *)
srr_run_to_sh tfibtbl_rtA_ok HS PC_UNWINDIMPL.
rename HF into HF1. clear HFr.
assert (FR1 : forall y : word, ~ (sp0 - ASTACK <= bv_unsigned y < sp0) -> ~ (T + t_unwinding <= bv_unsigned y < T + t_unwinding + 1) -> ms_mem ms y = mem0 y).
{ intros y Y1 Y2. apply HF1. intros Hw. destruct (windows_WIN E0 (ss_mem SS0m) _ (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw) as [X|X]; [exact (Y1 X) | exact (Y2 X)]. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape. rewrite Hshape.
rreg HS (2%bv : bv 5) Q2. rewrite E2 in Q2.
eapply SRr_bind.
(* AFh1.v:218-275, the unwinder's premises at AFgn.REG0 (region k of AFh1 is region k - 2 here). *)
{ apply (U1 W ly (ms_regs ms) (ms_mem ms) _ (sp0 - 2128) (pc_malloc_ra0 Tfib_code) sp0 (bv_unsigned (getr regs0 1)) (bv_unsigned (getr regs0 8)) ch LY IMG).
1:{ rreg HS (10%bv : bv 5) R; rewrite R, E2. unfold sp0. f_equal; zlia. }
1:{ rreg HS (11%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (12%bv : bv 5) R; rewrite R, E2. unfold sp0. symmetry. apply Z_to_bv_bv_unsigned. }
1:{ rreg HS (13%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (14%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
1:{ rreg HS (1%bv : bv 5) R; rewrite R. apply YK0s.ret_ok_even. reflexivity. }
1:{ cbv [pc_malloc_ra0 Tfib_code]; zlia. }
1:{ memv HS 1%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 5%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 6%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 26%nat 0%nat; [reflexivity | reflexivity | unfold TFIB_TSD; zlia]. }
1:{ memv HS 27%nat 0%nat; [reflexivity | cbn [sv_denot]; rewrite EaC; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 28%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite EaC; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; zlia); zlia
| cbn [sv_denot]; rewrite EaT; unfold w64; rewrite Zbv_add_unsigned; f_equal; unfold T; zlia | clear - LB; numconst; unfold T in *; zlia]. }
1:{ memv HS 29%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T; zlia | reflexivity | zlia]. }
1:{ memv HS 29%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T; zlia
| cbn [sv_denot]; rewrite EaTOP; unfold w64; rewrite Zbv_add_unsigned; f_equal; zlia | clear - LB; numconst; zlia]. }
1:{ memv HS 29%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T; zlia
| cbn [sv_denot]; rewrite EaTOP; unfold w64, ly_bot, kStackSpan; rewrite Zbv_add_unsigned; f_equal; zlia
| unfold ly_bot, kStackSpan; clear - LB; numconst; zlia]. }
1:{ memv HS 30%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T, t_unwinding; zlia | reflexivity | zlia]. }
1:{ eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 30 _ _ HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T; numconst; zlia | off_by ltac:(clear - LB; numconst; unfold T in *; zlia) ]. }
1:{ memv HS 21%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ memv HS 22%nat 0%nat; [reflexivity | reflexivity | zlia]. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia).
replace (bv_unsigned (getr regs0 2) + -2128) with (bv_unsigned (getr regs0 2) + (-133) * 16) by zlia. rewrite Z_mod_plus_full. exact Hsp_al. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia). clear - Hlo LB; numconst; unfold sp0 in *; zlia. }
1:{ intros a Ha. rewrite Q2 in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia).
eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ]. }
1:{ unfold sp0. replace (bv_unsigned (getr regs0 2) - 2128) with (bv_unsigned (getr regs0 2) + (- 266) * 8) by zlia.
rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ clear - Hlo LB; numconst; zlia. }
1:{ right. rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia). zlia. }
1:{ intros a Ha. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ]. }
1:{ clear; numconst; zlia. }
1:{ rewrite Q2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia). zlia. }
1:{ exact Hbot. }
1:{ exact Hhi. }
1:{ apply (mod0_factor _ 8 2); [zlia | exact Hsp_al]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 0%nat 11%nat;
[cbn [base_val YP09.r_base]; rewrite E2; unfold sp0; zlia | cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ apply val_mem_rdword; [apply u64_range|]. memv HS 0%nat 10%nat;
[cbn [base_val YP09.r_base]; rewrite E2; unfold sp0; zlia | cbn [sv_denot]; rewrite E8, Z.add_0_r; reflexivity | apply u64_range]. }
1:{ exact Hra4096. }
fold sp0 in Hch. destruct (sp0 + 16 <? ly_top ly) eqn:Hf0; [|exact Hch].
destruct (bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8))) eqn:Hb; [exact Hch|].
destruct Hch as [H16 Hfp]. split; [exact H16|].
apply Z.ltb_lt in Hf0.
unfold bad_next in Hb. apply Bool.orb_false_iff in Hb as [Hb _]. apply Bool.orb_false_iff in Hb as [Hb1 Hb2].
apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2.
eapply fpchain_ext2; [exact Hfp | zlia |].
intros a va Ha1 Ha2 Hva. eapply rdword_ext; [|exact Hva]. intros i Hi. apply aview_same.
apply (HF1 (Z_to_bv 64 (a + i))). intros Hw. rewrite unsigned_lit_small in Hw by (clear - Ha1 Ha2 H16 Hi Usp LB; numconst; zlia).
exact (WIN_not_high (a + i) ltac:(clear - Ha1 Ha2 H16 Hi Usp; zlia) (windows_WIN E0 (ss_mem SS0m) (a + i) (fun k _ => eq_refl) ltac:(vm_compute; reflexivity) Hw)). }
(* AFjh.v:527-603 (in the released file lib/A/AFjh.v, deleted in this series): the unwinder's return; the stack object's regions. *)
intros W' c' Hle (-> & regs1 & mem1 & mat1 & -> & HP & Hfr & Hpr & Ht1 & Ht2 & Ht3). srr_norm_model.
rreg HS (1%bv : bv 5) R1.
assert (Hfr' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite Q2 in Hfr. unfold w64, UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia).
apply Hfr; unfold sp0, ASTACK in *; zlia. }
assert (Hfr'' : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 64) -> mem1 x = ms_mem ms x).
{ intros x Hx. rewrite Q2 in Hfr. unfold w64, UNW_STK, BST_SIZE in Hfr. rewrite unsigned_lit_small in Hfr by (clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia).
apply Hfr; unfold sp0, ASTACK in *; zlia. }
jafter_call2 HS 54%nat regs1 (mrestrict (w_H W) mem1) HP (-64) (seq 0 30) HS1.
cbn [ms_mem restrict] in HS1.
lazymatch type of HS1 with Forall _ (?r0 :: ?tail) -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E0 (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1)) (r0 :: tail));
[ constructor;
[ eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0 - 64) _ Hfr'' Hpr); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi];
rewrite E2; intros a Ha; cbn beta; clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; first [zlia | right; zlia | left; zlia]
| apply Forall_forall; intros r Hr;
apply (in_map skel) in Hr; replace (map skel tail) with AFgn.SKEL_TAIL in Hr by (vm_compute; reflexivity);
pose proof (tail_facts E0 r (fun k _ => eq_refl) Hr) as (Y1 & Y2 & Y3 & Y4);
eapply (kept_of_frame E0 _ _ (fun a => sp0 - ASTACK <= a < sp0) _ Hfr' Hpr); intros a Ha; cbn beta;
[ clear - Y1 Y2 Y3 Ha; zlia | clear - Y4 Ha; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; zlia ] ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES1 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem1 a).
{ intros a Ha. apply Hpr. eapply (st_ok_window_apresent_off (w_H W) E0 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite E2; clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ]. }
set (En1 := havoc E0 54 (map (getr regs1) CLOB)) in HS1.
assert (HEn1 : forall k, (k < aHAVf)%nat -> ew En1 k = ew E0 k) by (intros k Hk; subst En1; apply ew_havoc_old; exact Hk).
apply (st_ok_add_region _ _ _ (YP09.mkRegion (Some 2%nat) (- ASTACK) (- IFRAME) (- ASTACK) (- IFRAME) [])) in HS1;
[ | reflexivity
| unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold IFRAME;
split; [clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia|]; split; [clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia|];
split; [intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Ho Usp Hlo LB; numconst; unfold sp0 in *; zlia) | apply PRES1; clear - Ho; numconst; unfold sp0 in *; zlia] | constructor]
| apply all_disjoint_of_forall; intros r' [<-|Hr'];
[ unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; unfold IFRAME; zlia
| apply (in_map skel) in Hr';
lazymatch type of Hr' with In _ (map skel ?tl) => replace (map skel tl) with AFgn.SKEL_TAIL in Hr' by (vm_compute; reflexivity) end;
pose proof (tail_facts En1 r' HEn1 Hr') as (Y1 & Y2 & Y3 & Y4);
unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2;
clear - Y1 Y2; unfold IFRAME, ASTACK in *; unfold sp0 in *; zlia ] ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
assert (OBJ0 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 2128) 8 (sp0 - 2112)).
{ eapply val_mem_frame; [intros k Hk; apply Hfr; rewrite ?Q2; unfold w64; rewrite ?unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; unfold sp0 in *; zlia); unfold UNW_STK, BST_SIZE; clear - Usp Hlo LB Hk; unfold sp0 in *; numconst; zlia|].
memv HS 0%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite E2; unfold sp0; zlia | cbn [sv_denot]; rewrite E2; unfold w64, sp0; first [f_equal; zlia | rewrite Zbv_add_unsigned; f_equal; zlia] | clear - Usp Hlo LB; numconst; unfold sp0 in *; zlia]. }
assert (LEN : (1 <= length tr <= 30)%nat).
{ unfold trm, call_trace. destruct (frame0_ok ly regs0); [apply unwind_of_chain_length | cbn; lia]. }
(* AFjh.v:570-579 (in the released file lib/A/AFjh.v, deleted in this series), the trace length with its upper word. *)
assert (OBJ1 : val_mem tfibsegs (mrestrict (w_H W) mem1) (sp0 - 2120) 8 LENv).
{ unfold LENm. replace (Z.of_nat (length tr)) with (Z.of_nat (length tr) + 2 ^ 32 * 0) by zlia.
apply val_mem_4_4; [zlia | zlia | |].
- eapply val_mem_addr; [exact Ht1 | zlia].
- assert (Z8 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120) 8 0)
by (memv HS 0%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite E2; unfold sp0; zlia | reflexivity | zlia]).
assert (Z4 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - 2120 + 4) 4 0).
{ intros k Hk. replace (sp0 - 2120 + 4 + Z.of_nat k) with (sp0 - 2120 + Z.of_nat (4 + k)) by zlia.
rewrite (Z8 (4 + k)%nat ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
eapply val_mem_frame; [intros k Hk; apply Hfr; rewrite ?Q2; unfold w64; rewrite ?unsigned_lit_small by (clear - Usp Hlo LB Hk; numconst; unfold sp0 in *; zlia); unfold UNW_STK, BST_SIZE; clear - Usp Hlo LB Hk; unfold sp0 in *; numconst; zlia| exact Z4]. }
rewrite <- (restrict_mkst_fx (w_H W)) in HS1. rewrite R1. clear HS. rename HS1 into HS.
(* AGji.v:411's first run (through asan_malloc), stopped at Allocate's entry (A 0x325b8, cf_pc_allocate). *)
srr_run_to_sh tfibtbl_rtA_ok HS PC_ALLOCATE.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En1 _ _ HS eq_refl) as HshA; cbn [ss_pc] in HshA.
(* The run's windows (AFh1.v:341-350's form): asan_malloc's frame below the stack object, the saved registers,
   T + t_unwinding. *)
assert (FRR : forall y : word, ~ (sp0 - ASTACK <= bv_unsigned y < sp0 - IFRAME) -> ~ (sp0 - 64 <= bv_unsigned y < sp0) ->
~ (T + t_unwinding <= bv_unsigned y < T + t_unwinding + 1) -> ms_mem msA y = mem1 y).
{ intros y Y1 Y2 Y3. apply HF. intros Hw. destruct (in_wrange_windows En1 _ _ Hw) as (b & lo & hi & Hin & Hr).
lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin];
[ injection Hin as <- <- <-; cbn [fst snd base_val] in Hr;
rewrite ?(HEn1 2%nat ltac:(cbv; zlia)), ?E2, ?(HEn1 32%nat ltac:(cbv; zlia)), ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by (clear - LB; numconst; unfold T in *; zlia);
clear - Y1 Y2 Y3 Hr; unfold IFRAME, ASTACK, t_unwinding in *; unfold sp0, T in *; zlia |]).
destruct Hin. }
pose proof stack_ivs as (IT & _).
assert (NT : forall a, sp0 - ASTACK <= a < sp0 -> ~ (T + t_unwinding <= a < T + t_unwinding + 1)).
{ intros a Ha Ht. clear - Ha Ht IT. unfold kThreadObjSize, t_unwinding, ASTACK in *. zlia. }
apply SRr_ret. unfold at_ALLOC. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg _ (with_vm_backing _ ?mt _) = _ /\ _ => exists (ms_regs msA), (ms_mem msA), mt end.
split. { rewrite HshA at 1. reflexivity. }
split. { rreg HS (1%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (2%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold w64, sp0. f_equal; zlia. }
split. { rreg HS (10%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (11%bv : bv 5) R; rewrite R, (HEn1 10%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (12%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (13%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)), E2. unfold w64, sp0. f_equal; zlia. }
split. { rreg HS (14%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (15%bv : bv 5) R; rewrite R. reflexivity. }
split. { rreg HS (8%bv : bv 5) R; rewrite R, (HEn1 2%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (9%bv : bv 5) R; rewrite R, (HEn1 10%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (3%bv : bv 5) R; rewrite R, (HEn1 3%nat ltac:(cbv; zlia)). apply Er. reflexivity. }
split. { rreg HS (4%bv : bv 5) R; rewrite R. reflexivity. }
split. { intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
repeat match type of Hr' with _ \/ _ => destruct Hr' as [Hr'|Hr'] end; subst r;
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
let kb := eval vm_compute in (Z_to_bv 5 k : bv 5) in
let RR := fresh "RR" in rreg HS kb RR; change (Z_to_bv 5 k) with kb; rewrite RR, HEn1 by (cbv; zlia); apply Er; reflexivity end. }
split. { intros x X1 X2.
rewrite (FRR x) by (first [exact X2 | intros HH; apply X1; clear - HH; unfold IFRAME, ASTACK in *; zlia]).
rewrite (Hfr' x X1). exact (FR1 x X1 X2). }
split. { memv HS 31%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 32%nat ltac:(cbv; zlia)), EaT; unfold w64; rewrite unsigned_lit_small by (clear - LB; numconst; unfold T in *; zlia); unfold T, t_unwinding; zlia | reflexivity | zlia]. }
split. { intros a Ha. destruct (Z_lt_le_dec a (sp0 - IFRAME)) as [A1|A1]; [|destruct (Z_lt_le_dec a (sp0 - 64)) as [A2|A2]].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 0 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; clear - Ha A1; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ].
- apply (apresent_same (w_H W) mem1); [|apply PRES1; exact Ha].
apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia);
[clear - A1; unfold IFRAME, ASTACK in *; zlia | clear - A2; zlia | exact (NT a Ha)].
- eapply (st_ok_window_apresent_off (w_H W) En1 _ _ 1 _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; clear - Ha A2; numconst; unfold sp0 in *; zlia
| off_by ltac:(clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia) ]. }
assert (FRM : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ms_mem msA (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
{ intros a Ha. apply FRR; rewrite unsigned_lit_small by (clear - Ha Usp Hlo LB; numconst; unfold sp0 in *; zlia);
[clear - Ha; unfold IFRAME, ASTACK in *; zlia | clear - Ha; zlia | apply NT; clear - Ha; unfold IFRAME, ASTACK in *; zlia]. }
split. { eapply val_mem_frame; [|exact OBJ0]. intros k Hk. apply FRM. unfold IFRAME. zlia. }
split. { eapply val_mem_frame; [|exact OBJ1]. intros k Hk. apply FRM. unfold IFRAME. zlia. }
split. { intros i Hi. eapply val_mem_addr; [eapply val_mem_frame; [|exact (Ht2 i Hi)] | zlia].
intros k Hk. apply FRM. unfold IFRAME. clear - Hi Hk LEN. zlia. }
split. { memv HS 1%nat 6%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 1%nat ltac:(cbv; zlia)), E1, Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 5%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 8%nat ltac:(cbv; zlia)), E8, Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 4%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 9%nat ltac:(cbv; zlia)), (Er 9 9%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 18%nat ltac:(cbv; zlia)), (Er 18 18%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 19%nat ltac:(cbv; zlia)), (Er 19 19%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 20%nat ltac:(cbv; zlia)), (Er 20 20%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 1%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 21%nat ltac:(cbv; zlia)), (Er 21 21%bv eq_refl), Z.add_0_r; reflexivity | apply u64_range]. }
split. { memv HS 0%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia
| cbn [sv_denot]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2, Z.add_0_r; reflexivity | exact Usp]. }
memv HS 0%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite (HEn1 2%nat ltac:(cbv; zlia)), E2; unfold sp0; zlia | reflexivity | unfold RA_ASAN_MALLOC, tfib_A____interceptor_malloc; zlia].
Qed.
End WK.
End c.
