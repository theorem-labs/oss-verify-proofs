(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMcdF.v (commit 67deba317dfb, blob 2b8b4fe2d652) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 7 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFex AFf2 AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFew AFff AFeu AFep AFeo AFgk AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFgy AFgz AFg0 AFez.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFk5 AFkn DMcdGk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FGsN FGtN DMcdGI DMcdGz DMcdGW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfk.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoG MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormHitG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMcdR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
#[local] Existing Instance AImgA.AImg_A.
#[local] Existing Instance ADIfaceA.DImg_A.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_qc, t_cache, t_cache_stats, t_unwinding, t_stats, KSTACK, TFIB_IMG_END, kBatchBytes, SHADOW_OFF, TFIB_TP, TFIB_TSD, TFIB_INST,
A_QUAR, A_ALLOCATOR, o_quar, o_space, o_rinfo, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize, kLowMemEnd in *.
Section g.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Hypothesis RMX : rmaxd_ok RMAXD.
Hypothesis RD : cd_reads B ARXr AOX DRq RMAXD.
Variables (inst : Z) (ly : alayout) (X : astate) (c off : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : cd_pre_cx B ARXr inst ly X c off W regs mem md.
Hypothesis MOD : cd_model RMAXD X c off.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Definition kcnt : Z := Z.of_nat (length (pc_chunks (cache X c))).
Definition kold : Z := fa_len (rg_free (reg X c)).
Definition kmf : Z := rg_mapped_fa (reg X c).
Lemma AR0 : ARXr inst ly X W mem md. Proof. exact (proj1 PRE). Qed.
Lemma GEO : layout_ok ly /\ img_cover ly /\ ly_tsd ly = TFIB_TSD. Proof. exact (cr_geo _ _ _ _ _ RD _ _ _ _ _ _ AR0). Qed.
Lemma IMG : img_cover ly. Proof. exact (proj1 (proj2 GEO)). Qed.
Let LO : layout_ok ly := proj1 GEO.
Lemma Hci : st_cache_inited X = true. Proof. exact (proj1 (proj2 MOD)). Qed.
Lemma Hc : 1 <= c <= 30. Proof. exact (proj1 MOD). Qed.
Lemma AINST : as_inst B = A_ALLOCATOR. Proof. rewrite (ts_inst _ TB). reflexivity. Qed.
Lemma PREF : inst = as_inst B /\ YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + KSTACK_CF <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - KSTACK_CF <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_cache) /\ getr regs 11 = w64 A_ALLOCATOR /\ getr regs 12 = w64 c /\
getr regs 13 = w64 (ly_space ly + off).
Proof.
destruct PRE as (_ & Hi & _ & Hra & Hra4 & Hal & Hlo & Hhi & HP & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3 & _).
rewrite Hi, AINST in Ha1. repeat (split; [assumption|]). assumption.
Qed.

Lemma BUDG : rg_mapped_fa (reg X c) < 4 * (fa_len (rg_free (reg X c)) + max_cached c / 2) ->
  eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md).
Proof. destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BG). exact BG. Qed.
Lemma HSP : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly.
Proof. pose proof PREF as (_ & _ & _ & _ & Hlo & Hhi & _). unfold spZ in *. unfold sp0. unfold KSTACK_CF, KSTACK in *. lia. Qed.
Local Notation Pv := (AFgk.Pv ly off).
Local Notation PCv := (AFgk.PCv ly c).
Local Notation MAXv := (AFgk.MAXv c).
Local Notation SZv := (AFgk.SZv c).
Local Notation Nv := (AFgk.Nv c).
Local Notation RIv := (AFgk.RIv ly).
Local Notation RGv := (AFgk.RGv ly c).
Local Notation RBv := (AFgk.RBv ly c).
Local Notation FAv := (AFgk.FAv ly c).
Local Notation RELv := (AFgk.RELv c off).
Lemma class_facts : 32 <= SZv <= kMaxSize /\ SZv mod 32 = 0 /\ 2 <= MAXv <= 16 /\ MAXv mod 2 = 0 /\ 1 <= Nv <= 8 /\ MAXv = 2 * Nv /\
region_off c = c * 2 ^ 32.
Proof.
pose proof (class_ok c ltac:(pose proof Hc; lia)) as (K1 & K2 & K3 & K4 & K5 & K6). unfold AFgk.Nv, AFgk.MAXv, AFgk.SZv, region_off.
rewrite Z.shiftl_mul_pow2 by (pose proof Hc; lia).
assert (32 <= class_size c) by (apply Z.mod_divide in K2 as [q Hq]; [|lia]; nia).
assert (D1 : 1 <= max_cached c / 2) by (apply Z.div_le_lower_bound; lia).
assert (D2 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
assert (D3 : max_cached c = 2 * (max_cached c / 2)) by (pose proof (Z.div_mod (max_cached c) 2 ltac:(lia)); lia).
repeat split; lia.
Qed.
Lemma reg_facts : 0 <= kold /\ 4 * kold <= kmf /\ 0 <= kmf <= kFreeArrayMax /\ kmf mod kFreeArrayMapSize = 0 /\
0 <= rg_alloc_user (reg X c) <= RMAXD /\ RMAXD <= kFreeArrayOffset /\
rg_alloc_user (reg X c) mod SZv = 0 /\ 0 <= kcnt <= MAXv /\ pc_max (cache X c) = MAXv /\
kold + max_cached c / 2 <= 2 ^ 27 /\ (kmf < 4 * (kold + max_cached c / 2) -> kmf + kFreeArrayMapSize <= kFreeArrayMax).
Proof.
destruct MOD as (_ & _ & C1 & C2 & O1 & O2 & O3 & O4 & A1 & A2 & F0 & F1 & F2 & F3 & F4 & F5).
destruct RMX as [R1 R2].
unfold kold, kmf, kcnt, AFgk.MAXv, AFgk.SZv. repeat split; try assumption; lia.
Qed.
Lemma off_facts : 0 <= RELv /\ RELv + SZv <= rg_alloc_user (reg X c) /\ RELv mod 16 = 0 /\ RELv mod SZv = 0.
Proof.
destruct MOD as (_ & _ & _ & _ & O1 & O2 & O3 & _). pose proof reg_facts as (_ & _ & _ & _ & _ & _ & AL & _). pose proof class_facts as (K1 & K2 & _).
unfold AFgk.RELv, AFgk.SZv in *.
apply Z.mod_divide in O3 as [q Hq]; [|lia]. apply Z.mod_divide in AL as [r Hr]; [|lia]. pose proof K2 as K2'. apply Z.mod_divide in K2 as [s Hs]; [|lia].
splits; [lia | | | apply Z.mod_divide; [lia|]; exists q; lia].
- assert (q < r) by nia. nia.
- apply Z.mod_divide; [lia|]. exists (q * (2 * s)). lia.
Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ SB mod 65536 = 0 /\
(T + kThreadObjSize <= ly_prim ly \/ ly_prim ly + kPrimResvSize <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_hi ly <= T) /\ (ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_hi ly <= ly_prim ly) /\
4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd /\ T mod 4096 = 0.
Proof.
pose proof (lo_high ly LO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (lo_app ly LO) as HA. pose proof (lo_disj ly LO) as HD0.
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. cbn beta in IT. cbn [fst snd] in IT.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD0 eq_refl eq_refl)) as ZT. clear HA IT.
pose proof (lo_space_in ly LO) as HSPC. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_space_al ly LO) as SAL.
pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
pose proof HD0 as HD. clear HD0. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
assert (I1 : 4096 <= as_inst B) by (rewrite AINST; unfold A_ALLOCATOR; lia).
assert (I2 : as_inst B + 3632 <= kLowMemEnd) by (rewrite AINST; unfold A_ALLOCATOR, kLowMemEnd; lia).
unfold zdisjoint in PT, PSTK, TSTK. cbn [fst snd] in *.
split; [clear - IP; lia|]. split; [clear - IP; lia|]. split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|].
clear - IP HSPC T1 T2 T3 T4 T5 T6 T7 SAL TAL PT PSTK TSTK I1 I2. unfold kHighMemBeg, kThreadObjSize, kPrimResvSize in *. repeat split; lia.
Qed.
Lemma derived : 4096 <= PCv /\ PCv + 80 <= T + kThreadObjSize /\     T + t_cache + 80 <= PCv /\ PCv + 80 <= T + t_cache + 2480 /\
RIv = SB + kRegionInfoOff /\ RGv = RIv + 128 * c /\ RIv + 128 <= RGv /\ RGv + 128 <= RIv + 4096 /\ kHighMemBeg <= RIv /\ RIv + 4096 <= ASAN_CEIL /\
RBv = SB + c * 2 ^ 32 /\ FAv = RBv + kFreeArrayOffset /\ SB + 2 ^ 32 <= RBv /\ RBv + 2 ^ 32 <= SB + 31 * 2 ^ 32 /\
Pv = RBv + RELv /\ kHighMemBeg <= SB /\ SB + kSpaceSize <= ASAN_CEIL.
Proof.
pose proof HI as HIx. pose proof Hc as Hcx. pose proof class_facts as (_ & _ & _ & _ & _ & _ & K7).
unfold AFgk.RGv, AFgk.FAv, AFgk.Pv. unfold AFgk.PCv, AFgk.RIv, AFgk.RBv, AFgk.RELv. rewrite K7.
numconst. repeat split; lia.
Qed.

Lemma cache_vals : val_mem tfibsegs m0 PCv 4 kcnt /\ val_mem tfibsegs m0 (PCv + 4) 4 MAXv /\ val_mem tfibsegs m0 (PCv + 8) 8 SZv.
Proof. destruct (cr_cache _ _ _ _ _ RD _ _ _ _ _ _ _ AR0 Hc Hci) as (A & Bv & Cv & _). exact (conj A (conj Bv Cv)). Qed.
Lemma slot_vals : forall (i : nat) v, nth_error (pc_chunks (cache X c)) i = Some v -> val_mem tfibsegs m0 (PCv + 16 + 4 * Z.of_nat i) 4 (v / 16).
Proof. destruct (cr_cache _ _ _ _ _ RD _ _ _ _ _ _ _ AR0 Hc Hci) as (_ & _ & _ & S). exact S. Qed.
Lemma region_vals :
val_mem tfibsegs m0 RGv 8 0 /\ val_mem tfibsegs m0 (RGv + 8) 8 0 /\ val_mem tfibsegs m0 (RGv + 16) 8 kold /\ val_mem tfibsegs m0 (RGv + 24) 8 kmf /\
val_mem tfibsegs m0 (RGv + 32) 8 (rg_alloc_user (reg X c)) /\ val_mem tfibsegs m0 (RGv + 40) 8 0 /\ val_mem tfibsegs m0 (RGv + 48) 8 (rg_mapped_user (reg X c)) /\
val_mem tfibsegs m0 (RGv + 56) 8 0.
Proof. exact (cr_region _ _ _ _ _ RD _ _ _ _ _ _ _ AR0 Hc). Qed.
Lemma val_mem_lo4 : forall m a w, 0 <= w < 2 ^ 64 -> val_mem tfibsegs m a 8 w -> val_mem tfibsegs m a 4 (w mod 2 ^ 32).
Proof.
intros m a w Hw H k Hk. rewrite (H k ltac:(lia)). do 2 f_equal. rewrite <- (le_byte_eq w). rewrite <- (le_byte_eq (w mod 2 ^ 32)).
rewrite <- (le_byte_split_lo (w mod 2 ^ 32) (w / 2 ^ 32) k); [| pose proof (Z.mod_pos_bound w (2 ^ 32)); lia | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia] | exact Hk].
f_equal. pose proof (Z.div_mod w (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma img_cells : Forall (cell_holds B ly rd0) (as_const B ly).
Proof. exact (cr_img _ _ _ _ _ RD _ _ _ _ _ _ AR0). Qed.
Lemma img_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros e w e' E. apply cell_holds_val_mem. apply (proj1 (Forall_forall _ _) img_cells).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma img_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
val_mem tfibsegs m0 a w x.
Proof. intros a w x E. exact (img_sym (ANum a) w (ANum x) E). Qed.
Lemma const_vals : val_mem tfibsegs m0 (A_ALLOCATOR + 32) 8 SB /\ val_mem tfibsegs m0 (A_ALLOCATOR + 48) 8 RIv /\
val_mem tfibsegs m0 (A_ALLOCATOR + 40) 4 4294967295 /\
val_mem tfibsegs m0 0xa1ff0 8 0x13a960 /\ val_mem tfibsegs m0 0x13a960 8 4096 /\ val_mem tfibsegs m0 0x103b8 8 0xafffff00000fffff.
Proof.
split.
{ replace (A_ALLOCATOR + 32) with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TB); reflexivity).
  replace SB with (aeval B ly (ASp 0)) by (cbn; lia). apply img_sym. vm_compute. reflexivity. }
split.
{ replace (A_ALLOCATOR + 48) with (aeval B ly (AInst o_rinfo)) by (cbn; rewrite (ts_inst B TB); reflexivity).
  replace RIv with (aeval B ly (ASp kRegionInfoOff)) by (cbn; unfold AFgk.RIv; reflexivity). apply img_sym. vm_compute. reflexivity. }
split.
{ change 4294967295 with (0xffffffff mod 2 ^ 32). apply val_mem_lo4; [lia|]. apply img_lit. vm_compute. reflexivity. }
split; [apply img_lit; vm_compute; reflexivity|]. split; [apply img_lit; vm_compute; reflexivity|].
apply img_lit. vm_compute. reflexivity.
Qed.
Lemma thread_present : forall a, T <= a < T + kThreadObjSize -> apresent H0 mem a.
Proof. exact (cr_thread _ _ _ _ _ RD _ _ _ _ _ _ AR0). Qed.
Lemma rinfo_present : forall a, RGv <= a < RGv + 128 -> apresent H0 mem a.
Proof. exact (cr_rinfo _ _ _ _ _ RD _ _ _ _ _ _ _ AR0 Hc). Qed.
Lemma fa_present : forall a, FAv <= a < FAv + kmf -> apresent H0 mem a.
Proof. exact (cr_fa _ _ _ _ _ RD _ _ _ _ _ _ _ AR0 Hc). Qed.
Lemma stack_present : forall a, sp0 - KSTACK <= a < sp0 -> apresent H0 mem a.
Proof. pose proof PREF as (_ & _ & _ & _ & _ & _ & HP & _). unfold spZ in HP. intros a Ha. apply HP. fold sp0. unfold KSTACK_CF, KSTACK in *. lia. Qed.
Lemma word_of_present : forall a, (forall i, 0 <= i < 8 -> apresent H0 mem (a + i)) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs m0 a 8 w.
Proof.
intros a PR.
assert (BY : forall k, (k < 8)%nat -> exists b, mbyte tfibsegs m0 (a + Z.of_nat k) = Some b).
{ intros k Hk. apply apresent_mbyte. apply PR. lia. }
destruct (BY 0%nat ltac:(lia)) as [b0 B0]. destruct (BY 1%nat ltac:(lia)) as [b1 B1]. destruct (BY 2%nat ltac:(lia)) as [b2 B2]. destruct (BY 3%nat ltac:(lia)) as [b3 B3].
destruct (BY 4%nat ltac:(lia)) as [b4 B4]. destruct (BY 5%nat ltac:(lia)) as [b5 B5]. destruct (BY 6%nat ltac:(lia)) as [b6 B6]. destruct (BY 7%nat ltac:(lia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
split; [lia|].
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> YG0f.le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold YG0f.le_byte. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); lia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfibsegs m0 (a + Z.of_nat kk) = Some bk -> YG0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfibsegs m0 (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, <- le_byte_eq, Hl, Z_to_bv_bv_unsigned. reflexivity. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|lia];
[ apply (GOAL b0 0%nat B0) | apply (GOAL b1 1%nat B1) | apply (GOAL b2 2%nat B2) | apply (GOAL b3 3%nat B3)
| apply (GOAL b4 4%nat B4) | apply (GOAL b5 5%nat B5) | apply (GOAL b6 6%nat B6) | apply (GOAL b7 7%nat B7) ]; subst WW.
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | change (2 ^ (8 * Z.of_nat 0)) with 1; lia | lia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia | lia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia | lia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia | lia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; lia | lia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; lia | lia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [lia | lia | lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; lia | lia].
Qed.
Lemma byte_of_present : forall a, apresent H0 mem a -> exists v, 0 <= v < 2 ^ 8 /\ val_mem tfibsegs m0 a 1 v.
Proof.
intros a PR. assert (BY : exists b, mbyte tfibsegs m0 a = Some b) by (apply apresent_mbyte; exact PR). destruct BY as [b Bb].
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
exists (bv_unsigned b). split; [change (2 ^ 8) with 256; lia|].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Bb. f_equal.
rewrite <- le_byte_eq. unfold YG0f.le_byte. cbn [Z.of_nat Z.mul Pos.mul].
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. change (2 ^ 8) with 256.
rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma junk_vals : exists j80 j88 jst,
(0 <= j80 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 80) 8 j80) /\ (0 <= j88 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 88) 8 j88) /\
(0 <= jst < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_cache + 2576) 8 jst).
Proof.
destruct (word_of_present (RGv + 80)) as (w0 & R0 & V0); [intros i Hi; apply rinfo_present; lia|].
destruct (word_of_present (RGv + 88)) as (w1 & R1 & V1); [intros i Hi; apply rinfo_present; lia|].
destruct (word_of_present (T + t_cache + 2576)) as (w2 & R2 & V2); [intros i Hi; apply thread_present; numconst; lia|].
exists w0, w1, w2. repeat split; assumption || lia.
Qed.
Section h.
Variables (j80 j88 jst : Z).
Hypothesis HJ80 : 0 <= j80 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 80) 8 j80.
Hypothesis HJ88 : 0 <= j88 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 88) 8 j88.
Hypothesis HJST : 0 <= jst < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_cache + 2576) 8 jst.
Local Notation E0 := (AFgk.E0 ly regs c off kcnt kold kmf j80 j88 jst).
Lemma E2 : ew E0 2 = getr regs 2. Proof. exact (AFgk.E2 ly regs c off kcnt kold kmf j80 j88 jst). Qed.
Lemma chunk_lit : forall base a (w : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k0 x, ew E0 k0 = w64 x -> 0 <= x < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k0 0))).
Proof.
intros base a w k0 x Hk0 Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk0. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) AFgk.REG0.
Proof.
pose proof HSP as [S1 S2]. pose proof HI as HIx. pose proof derived as DR. pose proof reg_facts as RF. pose proof class_facts as KF.
pose proof cache_vals as (C1 & C2 & C3). pose proof const_vals as (V1 & V2 & V3 & V4 & V5 & V6). pose proof HJST as [J1 J2].
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (BV2 : bv_unsigned (ew E0 2) = sp0) by (rewrite E2; reflexivity).
unfold AFgk.REG0, AFgk.R_STK_HI, AFgk.R_STK_LO, AFgk.R_PC, AFgk.R_JST, fatom8, flit8, flit4.
apply Forall_cons.
{ reg_intro. rewrite BV2. split; [clear - S1 S2 HIx; numconst; lia|]. split; [clear - S1 S2 HIx Usp; numconst; lia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable; [clear - S1 S2 HIx Ho; numconst; lia|]. apply stack_present. clear - Ho. numconst. lia. }
apply Forall_cons.
{ reg_intro. rewrite BV2. split; [clear - S1 S2 HIx; numconst; lia|]. split; [clear - S1 S2 HIx Usp; numconst; lia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable; [clear - S1 S2 HIx Ho; numconst; lia|]. apply stack_present. clear - Ho. numconst. lia. }
apply Forall_cons.
{ reg_intro. rewrite AFgk.EqPC. unfold w64. rewrite unsigned_lit_small by (clear - DR HIx; numconst; lia).
split; [clear - DR HIx; numconst; lia|]. split; [clear - DR HIx; numconst; lia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); clear - DR Ho; numconst; lia|]. apply thread_present. clear - Ho DR. numconst. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_atom _ _ 4 37%nat kcnt); [reflexivity | clear - RF KF; lia | rewrite Z.add_0_r; exact C1 | clear - RF KF; r4 | cbn; lia].
- apply (chunk_atom _ _ 4 38%nat MAXv); [reflexivity | clear - KF; lia | exact C2 | clear - KF; r4 | cbn; lia].
- apply (chunk_atom _ _ 8 39%nat SZv); [reflexivity | clear - KF; numconst; lia | exact C3 | clear - KF; numconst; r8 | cbn; lia]. }
apply Forall_cons.
{ reg_intro. rewrite AFgk.EqT. unfold w64. rewrite unsigned_lit_small by (clear - HIx; numconst; lia).
split; [clear - HIx; numconst; lia|]. split; [clear - HIx; numconst; lia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); clear - Ho; numconst; lia|]. apply thread_present. clear - Ho. numconst. lia. }
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom _ _ 8 48%nat jst); [reflexivity | exact J1 | rewrite Z.add_assoc; exact J2 | r8 | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom 0 _ 8 33%nat SB); [reflexivity | clear - DR; numconst; lia | rewrite Z.add_0_l; exact V1 | clear - DR; numconst; r8 | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_atom 0 _ 8 49%nat RIv); [reflexivity | clear - DR; numconst; lia | rewrite Z.add_0_l; exact V2 | clear - DR; numconst; r8 | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [numconst; lia|]. split; [numconst; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 4); [rewrite Z.add_0_l; exact V3 | cbn; lia | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 8); [rewrite Z.add_0_l; exact V4 | cbn; lia | cbn; lia]. }
apply Forall_cons.
{ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 8); [rewrite Z.add_0_l; exact V5 | cbn; lia | cbn; lia]. }
apply Forall_cons; [|apply Forall_nil].
{ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_lit 0 _ 8); [rewrite Z.add_0_l; exact V6 | cbn; lia | cbn; lia]. }
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 AFgk.REG0.
Proof.
pose proof HSP as [S1 S2]. pose proof HI as HIx. pose proof derived as DR.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply pairwise_disjoint_of_extents. unfold AFgk.REG0, AFgk.R_STK_HI, AFgk.R_STK_LO, AFgk.R_PC, AFgk.R_JST, fatom8, flit8, flit4, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E2, AFgk.EqPC, AFgk.EqT. unfold w64. fold sp0. numconst. rewrite !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms AFgk.FFK).
Proof.
pose proof HSP as [S1 S2]. pose proof HI as HIx. pose proof derived as DR. pose proof reg_facts as RF. pose proof class_facts as KF. pose proof off_facts as OFF.
pose proof HJ80 as [A1 _]. pose proof HJ88 as [A2 _]. pose proof HJST as [A3 _]. pose proof Hc as Hcx.
pose proof PREF as (_ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (E2' : ew E0 2 = w64 sp0) by (rewrite E2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
pose proof HIx as (_ & _ & _ & _ & _ & _ & _ & _ & SAL & _ & _ & _ & _ & _ & TAL).
assert (T16 : exists q, T = 4096 * q) by (apply Z.mod_divide in TAL as [q Hq]; [|lia]; exists q; lia). destruct T16 as [qT HqT].
assert (PC16 : PCv mod 2 ^ 4 = 0).
{ unfold AFgk.PCv, t_cache. rewrite HqT. apply Z.mod_divide; [lia|]. exists (256 * qT + 13 + 5 * c). change (2 ^ 4) with 16. lia. }
assert (P16 : Pv mod 2 ^ 4 = 0).
{ destruct DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB & _ & _ & _ & EP & _). rewrite EP, RB. destruct OFF as (_ & _ & O3 & _).
apply Z.mod_divide in SAL as [q Hq]; [|lia]. apply Z.mod_divide in O3 as [q3 Hq3]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 4096 + c * 2 ^ 28 + q3). change (2 ^ 4) with 16. lia. }
assert (RI12 : RIv mod 2 ^ 12 = 0).
{ destruct DR as (_ & _ & _ & _ & ERI & _). rewrite ERI. apply Z.mod_divide in SAL as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 16 + 2 ^ 25). unfold kRegionInfoOff. change (2 ^ 12) with 4096. lia. }
assert (RG7 : RGv mod 2 ^ 7 = 0).
{ destruct DR as (_ & _ & _ & _ & _ & ERG & _). rewrite ERG. pose proof RI12 as RI12'. apply Z.mod_divide in RI12' as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q * 32 + c). change (2 ^ 7) with 128. change (2 ^ 12) with 4096 in Hq. lia. }
assert (SLOT4 : AFgk.SLOTv ly c kcnt mod 2 ^ 2 = 0).
{ unfold AFgk.SLOTv, AFgk.PCv, t_cache. rewrite HqT. apply Z.mod_divide; [lia|]. exists (1024 * qT + 52 + 20 * c + 4 + AFgk.CNTPv c kcnt). change (2 ^ 2) with 4. lia. }
assert (DST2 : AFgk.DSTv ly c kold mod 2 ^ 2 = 0 /\ AFgk.SRCv ly c kcnt mod 2 ^ 2 = 0).
{ unfold AFgk.DSTv, AFgk.SRCv. destruct DR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB & EFA & _). rewrite EFA, RB.
pose proof SAL as SAL'. apply Z.mod_divide in SAL' as [q Hq]; [|lia]. change (2 ^ 2) with 4. split.
- apply Z.mod_divide; [lia|]. exists (q * 16384 + c * 2 ^ 30 + 939524096 + kold). unfold kFreeArrayOffset. rewrite Hq. lia.
- apply Z.mod_divide; [lia|]. unfold AFgk.PCv, t_cache. rewrite HqT. exists (qT * 1024 + 52 + 20 * c + 4 + (kcnt - Nv)). lia. }
destruct DST2 as [DST2 SRC2].
assert (CNTP : 0 <= AFgk.CNTPv c kcnt < MAXv) by (unfold AFgk.CNTPv; destruct (Z.eqb_spec kcnt MAXv); clear - RF KF e || clear - RF KF n; lia).
cbn [AFgk.FFK f_atoms atoms_ok]. numconst.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 HIx Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat T); [reflexivity| | | |]. all: clear - CR0 HIx TAL; first [lia | change (2 ^ 12) with 4096; exact TAL]. }
split. { apply (AF 33%nat SB); [reflexivity| | | |]. all: clear - CR0 HIx DR SAL; first [lia | apply Z.mod_divide in SAL as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists q; change (2 ^ 16) with 65536; lia]. }
split. { apply (AF 34%nat Pv); [reflexivity| | | |]. all: clear - CR0 HIx DR OFF RF KF P16; first [lia | exact P16]. }
split. { apply (AF 35%nat c); [reflexivity| | | |]. all: clear - CR0 Hcx; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 36%nat PCv); [reflexivity| | | |]. all: clear - CR0 HIx DR PC16; first [lia | exact PC16]. }
split. { apply (AF 37%nat kcnt); [reflexivity| | | |]. all: clear - CR0 RF KF; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat MAXv); [reflexivity| | | |]. all: clear - CR0 KF; first [lia | change (2 ^ 1) with 2; tauto]. }
split. { apply (AF 39%nat SZv); [reflexivity| | | |]. all: clear - CR0 KF; first [lia | destruct KF as (_ & K2 & _); apply Z.mod_divide in K2 as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists q; change (2 ^ 5) with 32; lia]. }
split. { apply (AF 40%nat (AFgk.SLOTv ly c kcnt)); [reflexivity| | | |]. all: unfold AFgk.SLOTv in *; clear - CR0 HIx DR CNTP KF SLOT4; first [lia | exact SLOT4]. }
split. { apply (AF 41%nat RGv); [reflexivity| | | |]. all: clear - CR0 DR RG7; first [lia | exact RG7]. }
split. { apply (AF 42%nat kold); [reflexivity| | | |]. all: clear - CR0 RF; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 43%nat kmf); [reflexivity| | | |]. all: clear - CR0 RF; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 44%nat (AFgk.DSTv ly c kold)); [reflexivity| | | |]. all: unfold AFgk.DSTv in *; clear - CR0 DR RF KF DST2; first [lia | exact DST2]. }
split. { apply (AF 45%nat (AFgk.SRCv ly c kcnt)); [reflexivity| | | |]. all: unfold AFgk.SRCv in *; clear - CR0 HIx DR RF KF SRC2; first [lia | exact SRC2]. }
split. { apply (AF 46%nat j80); [reflexivity| | | |]. all: clear - CR0 A1; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 47%nat j88); [reflexivity| | | |]. all: clear - CR0 A2; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 48%nat jst); [reflexivity| | | |]. all: clear - CR0 A3; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 49%nat RIv); [reflexivity| | | |]. all: clear - CR0 DR RI12; first [lia | exact RI12]. }
Qed.
Lemma SEED_ok : st_ok tfibsegs E0 AFgk.SS0 (restrict (w_H W) (mkst regs (w64 0x34c14) mem (seg_rom tfibsegs))).
Proof.
pose proof PREF as (_ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1 & Ha2 & Ha3). rewrite (ts_tp _ TB) in Htp.
pose proof HI as (_ & _ & hT1 & hT2 & _).
rewrite restrict_mkst_fx. unfold AFgk.SS0, AFgk.SR0, sr_set. cbn [bv_eqb]. unfold AFgk.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Htp] | intros XX; discriminate |] | intros XX; discriminate | cbn [sv_denot]; exact Ha1] | intros XX; discriminate |] | intros XX; discriminate |].
+ cbn [sv_denot]. fold (AFgk.E0 ly regs c off kcnt kold kmf j80 j88 jst). rewrite AFgk.EqT, Ha0. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (AFgk.E0 ly regs c off kcnt kold kmf j80 j88 jst). rewrite AFgk.EqC, Ha2. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
+ cbn [sv_denot]. fold (AFgk.E0 ly regs c off kcnt kold kmf j80 j88 jst). rewrite AFgk.EqP, Ha3. unfold w64, AFgk.Pv. rewrite Zbv_add_unsigned. f_equal. lia.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [exact FACTS_ok | split; exact I].
Qed.

Local Ltac dnu := repeat (first [ progress unfold DMcdGk.SLOTv in * | progress unfold DMcdGk.CNTPv in * | progress unfold DMcdGk.MAXv in * | progress unfold DMcdGk.Nv in * | progress unfold DMcdGk.SRCv in * | progress unfold DMcdGk.DSTv in * | progress unfold DMcdGk.FAv in * | progress unfold DMcdGk.RBv in * | progress unfold DMcdGk.PCv in * | progress unfold DMcdGk.RGv in * | progress unfold DMcdGk.RELv in * | progress unfold DMcdGk.SZv in * | progress unfold DMcdGk.RIv in * | progress unfold DMcdGk.Pv in * | progress unfold AFgk.SLOTv in * | progress unfold AFgk.CNTPv in * | progress unfold AFgk.MAXv in * | progress unfold AFgk.Nv in * | progress unfold AFgk.SRCv in * | progress unfold AFgk.DSTv in * | progress unfold AFgk.FAv in * | progress unfold AFgk.RBv in * | progress unfold AFgk.PCv in * | progress unfold AFgk.RGv in * | progress unfold AFgk.RELv in * | progress unfold AFgk.SZv in * | progress unfold AFgk.RIv in * | progress unfold AFgk.Pv in * ]).
Theorem FHG_ok : DMcdGk.free_hyps W ly regs mem c off kcnt kold kmf j80 j88 jst.
Proof.
pose proof PREF as (_ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof reg_facts as RF. pose proof class_facts as KF. pose proof off_facts as OFF. pose proof derived as DR. pose proof HI as HIx.
pose proof region_vals as (R0 & _ & R16 & R24 & _). pose proof HJ80 as [A1 B1]. pose proof HJ88 as [A2 B2]. pose proof HJST as [A3 B3].
constructor.
all: try dnu.
- exact LO.
- exact IMG.
- rewrite (ts_tp _ TB) in Htp. exact Htp.
- exact Hra.
- exact Hra4.
- exact HSP.
- exact Hal.
- exact stack_present.
- exact Hc.
- clear - RF. unfold kcnt, DMcdGk.MAXv, AFgk.MAXv in *. lia.
- destruct OFF as (O1 & O2 & O3 & _). destruct RF as (_ & _ & _ & _ & [AU0 AU] & MU & _). unfold DMcdGk.RELv, DMcdGk.SZv, AFgk.RELv, AFgk.SZv in *. split; [exact O1|]. split; [clear - O2 AU MU; lia | exact O3].
- intros a Ha. apply thread_present. pose proof DR as DRx. pose proof KF as (_ & _ & K3 & _ & K5 & K6 & _).
pose proof RF as (_ & _ & _ & _ & _ & _ & _ & [Rc0 Rc1] & _).
destruct (Z.eqb_spec kcnt (max_cached c)) as [E|E]; clear - Ha DRx K3 K5 K6 Rc0 Rc1 E; numconst; unfold kcnt in *; lia.
- clear - A1 A2 A3. tauto.
- intros Hf.
destruct RF as (F0 & F1 & [F2 F3] & _ & _ & _ & _ & _ & _ & F27 & _).
split; [exact F0|]. split; [exact F1|]. split; [exact F3|]. split; [unfold DMcdGk.Nv; exact F27|]. split; [exact rinfo_present|].
split; [exact R0|]. split; [exact R16|]. split; [exact R24|]. split; [exact B1|]. split; [exact B2|]. split.
+ intros a Ha. apply thread_present. pose proof DR as (D1 & D2 & D3 & _). pose proof KF as (_ & _ & K3 & _ & K5 & K6 & _). dnu. clear - Ha D1 D2 D3 K3 K5 K6 Hf. unfold t_cache in *. lia.
+ intros a Ha. apply fa_present. dnu. clear - Ha F0. lia.
- exact SEED_ok.
Qed.

Hypothesis NOGROW : kcnt = MAXv -> 4 * (kold + Nv) <= kmf.
Theorem FH_ok : AFgk.free_hyps W ly regs mem c off kcnt kold kmf j80 j88 jst.
Proof.
pose proof PREF as (_ & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof reg_facts as RF. pose proof class_facts as KF. pose proof off_facts as OFF. pose proof derived as DR. pose proof HI as HIx.
pose proof region_vals as (R0 & _ & R16 & R24 & _). pose proof HJ80 as [A1 B1]. pose proof HJ88 as [A2 B2]. pose proof HJST as [A3 B3].
constructor.
- exact LO.
- exact IMG.
- rewrite (ts_tp _ TB) in Htp. exact Htp.
- exact Hra.
- exact Hra4.
- exact HSP.
- exact Hal.
- exact stack_present.
- exact Hc.
- clear - RF. unfold kcnt in *. lia.
- destruct OFF as (O1 & O2 & O3 & _). destruct RF as (_ & _ & _ & _ & [AU0 AU] & MU & _). split; [exact O1|]. split; [clear - O2 AU MU; lia | exact O3].
- intros a Ha. apply thread_present. unfold AFgk.SLOTv in Ha.
assert (CNTP : 0 <= AFgk.CNTPv c kcnt < MAXv) by (unfold AFgk.CNTPv; destruct (Z.eqb_spec kcnt MAXv); clear - RF KF e || clear - RF KF n; lia).
clear - Ha DR KF CNTP. numconst. lia.
- clear - A1 A2 A3. tauto.
- intros Hf. pose proof (NOGROW Hf) as NG.
split; [clear - RF; lia|]. split; [exact NG|].
split; [clear - RF; lia|]. split; [exact rinfo_present|].
split; [exact R0|]. split; [exact R16|]. split; [exact R24|]. split; [exact B1|]. split; [exact B2|]. split.
+ intros a Ha. apply fa_present. unfold AFgk.DSTv, AFgk.Nv, AFgk.MAXv, kmf in *. clear - Ha RF KF NG. lia.
+ intros a Ha. apply thread_present. pose proof DR as (D1 & D2 & D3 & _). pose proof KF as (_ & _ & K3 & _ & K5 & K6 & _). unfold AFgk.SRCv in Ha. clear - Ha D1 D2 D3 K3 K5 K6 Hf. unfold t_cache in *. lia.
- exact SEED_ok.
Qed.
End h.

Local Notation WINk := (AFgk.WIN ly regs c kcnt kold).
Local Notation SLOTv' := (AFgk.SLOTv ly c kcnt).
Local Notation DSTv' := (AFgk.DSTv ly c kold).
Lemma wvb_self_l : forall md', with_vm_backing (m_vm_lazy md') (m_vm_materialized md') md' = md'.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_l : forall md' mat, same_io md' (with_vm_backing (m_vm_lazy md') mat md').
Proof. intros md' mat. unfold same_io. destruct md'; cbn; repeat split; reflexivity. Qed.
Lemma HLEN : (32 <= length (st_cache X))%nat /\ (32 <= length (st_regions X))%nat.
Proof. exact (cr_len _ _ _ _ _ RD _ _ _ _ _ _ AR0). Qed.
Lemma HLc : (Z.to_nat c < length (st_cache X))%nat. Proof. pose proof HLEN as [L _]. pose proof Hc. lia. Qed.
Lemma HLr : (Z.to_nat c < length (st_regions X))%nat. Proof. pose proof HLEN as [_ L]. pose proof Hc. lia. Qed.
Lemma S'_cinit_l : st_cache_inited (AFez.S' X c off) = true.
Proof. unfold AFez.S', AFez.X1. destruct (AFez.full X c); cbn; exact Hci. Qed.
Lemma model_step : (kcnt = MAXv -> 4 * (kold + Nv) <= kmf) -> cache_dealloc c off X = IRet (tt, AFez.S' X c off).
Proof.
intros NG. pose proof reg_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PM & _). pose proof class_facts as (_ & _ & K3 & _ & K5 & K6 & _).
unfold AFez.S', AFez.X1, AFez.full.
destruct (Z.of_nat (length (pc_chunks (cache X c))) =? max_cached c) eqn:E.
- apply Z.eqb_eq in E. specialize (NG E).
  assert (LK : length (YFfh.kdrained c X) = Z.to_nat Nv).
  { unfold YFfh.kdrained. cbv zeta. rewrite PM, length_skipn. change (AFgk.MAXv c / 2) with (AFgk.Nv c).
    unfold AFgk.MAXv in *. clear - E K5 K6. lia. }
  apply YFfh.cache_dealloc_eq_full; [exact Hci | pose proof Hc; lia | exact HLc | rewrite PM; exact E |].
  rewrite LK, Z2Nat.id by lia. exact NG.
- apply Z.eqb_neq in E. apply YFfh.cache_dealloc_eq_push; [exact Hci | rewrite PM; exact E].
Qed.
Lemma win_zone_mn : forall (x : word),
(sp0 - KSTACK <= bv_unsigned x < sp0) \/ (ly_T ly <= bv_unsigned x < ly_T ly + kThreadObjSize) \/
(ly_prim ly <= bv_unsigned x < ly_prim ly + kPrimResvSize) -> MemnormT.mn_safe tfibsegs x.
Proof.
intros x Hz. destruct Hz as [Hz|[Hz|Hz]].
- apply MemnormHitG.mn_safe_high. pose proof HI as (_ & _ & _ & _ & hS1 & hS2 & _). pose proof HSP as [S1 S2].
  clear - Hz hS1 hS2 S1 S2. unfold KSTACK, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
- exact (MemnormHitG.mn_safe_owned ly (ly_T ly, kThreadObjSize) x LO IMG
    ltac:(unfold owned_extents; right; right; left; reflexivity) Hz).
- exact (MemnormHitG.mn_safe_owned ly (ly_prim ly, kPrimResvSize) x LO IMG
    ltac:(unfold owned_extents; left; reflexivity) Hz).
Qed.
Lemma CNTP_range : 0 <= AFgk.CNTPv c kcnt < MAXv.
Proof.
pose proof reg_facts as (_ & _ & _ & _ & _ & _ & _ & [R0 R1] & _). pose proof class_facts as (_ & _ & K3 & _ & K5 & K6 & _).
unfold AFgk.CNTPv. destruct (Z.eqb_spec kcnt MAXv); clear - R0 R1 K3 K5 K6 e || clear - R0 R1 K3 K5 K6 n; lia.
Qed.
Lemma WIN_zone : forall a, WINk a -> (sp0 - 320 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof HI as HIx. pose proof derived as DR. pose proof CNTP_range as CNTP.
pose proof reg_facts as (F0 & F1 & [F2 F3] & _ & _ & _ & _ & _ & _ & F10 & _). pose proof class_facts as (_ & _ & K3 & _ & K5 & K6 & K7).
unfold AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[Hw|[Hf Hw]]].
- left. exact Hw.
- right; left. unfold AFgk.SLOTv in Hw. clear - Hw DR CNTP K3. unfold t_cache, kThreadObjSize in *. lia.
- right; right. unfold AFgk.DSTv, AFgk.FAv, AFgk.RBv in Hw. destruct HIx as (_ & _ & _ & _ & _ & _ & hSB1 & hSB2 & _).
  destruct DR as (_ & _ & _ & _ & D5 & D6 & D7 & D8 & _).
  unfold kold, AFgk.Nv, AFgk.MAXv in *. rewrite K7 in Hw. pose proof Hc as Hcc. clear - Hw hSB1 hSB2 D5 D6 D7 D8 F0 F10 K5 K6 Hcc.
  unfold kSpaceSize, kRegionInfoOff, kFreeArrayOffset, kPrimResvSize in *. lia.
Qed.
Lemma WIN_dec : forall a, WINk a \/ ~ WINk a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
assert (EF : kcnt = MAXv \/ kcnt <> MAXv) by lia.
unfold AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG. fold sp0.
destruct (EM (sp0 - 320) sp0) as [C|C0]; [left; left; exact C|].
destruct (EM PCv (PCv + 4)) as [C|C1]; [left; right; left; left; exact C|].
destruct (EM SLOTv' (SLOTv' + 4)) as [C|C2]; [left; right; left; right; left; exact C|].
destruct (EM (T + t_cache + 2576) (T + t_cache + 2584)) as [C|C3]; [left; right; left; right; right; exact C|].
destruct EF as [EF|EF].
- destruct (EM RGv (RGv + 8)) as [C|C4]; [left; do 2 right; split; [exact EF | left; left; exact C]|].
  destruct (EM (RGv + 16) (RGv + 24)) as [C|C5]; [left; do 2 right; split; [exact EF | left; right; left; exact C]|].
  destruct (EM (RGv + 80) (RGv + 88)) as [C|C6]; [left; do 2 right; split; [exact EF | left; right; right; exact C]|].
  destruct (EM DSTv' (DSTv' + 4 * Nv)) as [C|C7]; [left; do 2 right; split; [exact EF | right; exact C]|].
  right. intros [X0|[[X1|[X2|X3]]|[_ [[X4|[X5|X6]]|X7]]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (C4 X4) | exact (C5 X5) | exact (C6 X6) | exact (C7 X7)].
- right. intros [X0|[[X1|[X2|X3]]|[X4 _]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (EF X4)].
Qed.

Definition cd_postR (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\ MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> ImgBaseDG.YFeuC.puser ly X a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, ImgBaseDG.YFeuC.puser ly X a -> ImgBaseDG.YFeuC.puser ly (snd r) a) /\
  st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a).

Definition SG : astate := YFfh.XK_push c off (YFfh.XK_drain c (YG06.upd_reg c (FGcN.rgG (reg X c)) X)).
Definition cd_postS (r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  cd_postR r W' c' /\ (((kcnt = MAXv -> 4 * (kold + Nv) <= kmf) /\ snd r = AFez.S' X c off) \/
                     (kcnt = MAXv /\ kmf < 4 * (kold + Nv) /\ snd r = SG)).
Lemma alloc_S' : forall c', 0 <= c' -> rg_alloc_user (reg (AFez.S' X c off) c') = rg_alloc_user (reg X c').
Proof.
intros c' Hc'. unfold AFez.S', YFfh.XK_push. cbv zeta. rewrite reg_upd_pc. unfold AFez.X1.
destruct (AFez.full X c); [|reflexivity]. unfold YFfh.XK_drain. cbv zeta. rewrite reg_upd_pc.
destruct (Z.eq_dec c' c) as [->|NE].
- rewrite reg_upd_reg; [reflexivity | pose proof Hc; lia | exact HLr].
- rewrite reg_upd_reg_other; [reflexivity | pose proof Hc; lia | exact Hc' | intros E; exact (NE (eq_sym E))].
Qed.

Lemma WIN_owned : forall a, WINk a -> ~ (sp0 - 320 <= a < sp0) -> AOX ly X a.
Proof.
intros a Hw Hs. apply (cr_own _ _ _ _ _ RD _ _ _ _ _ _ c off AR0 MOD).
unfold AFgk.WIN in Hw. fold sp0 in Hw. destruct Hw as [Hw|Hw]; [exfalso; exact (Hs Hw) | exact Hw].
Qed.

Lemma errno_not_WIN : forall i, 0 <= i < 4 -> ~ WINk (as_errno B + i).
Proof.
intros i Hi Hw. pose proof (WIN_zone _ Hw) as Z. rewrite (ts_errno _ TB) in Z.
pose proof HI as (hP1 & _ & hT1 & _ & hS1 & _). pose proof HSP as [S1 S2].
clear - Z Hi hP1 hT1 hS1 S1. unfold TFIB_ERRNO, zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, KSTACK, kThreadObjSize in *. lia.
Qed.

Lemma puser_not_WIN : forall a, ImgBaseDG.YFeuC.puser ly X a -> ~ WINk a.
Proof.
intros a (c' & Hc' & Hr) Hw.
pose proof (cr_user _ _ _ _ _ RD _ _ _ _ _ _ c' AR0 Hc') as ([U0 U1'] & U1'' & _). assert (U1 : rg_alloc_user (reg X c') <= kFreeArrayOffset) by lia.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSB1 & hSB2 & _ & hTP & _ & hSP & _).
pose proof derived as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & _).
pose proof reg_facts as (F0 & F1 & [F2 F3] & _ & [A0 A1] & R1 & _ & _ & _ & F10 & _).
pose proof class_facts as (_ & _ & K3 & _ & K5 & K6 & K7). pose proof CNTP_range as CNTP. pose proof HSP as [S1 S2]. pose proof Hc as Hcc.
unfold region_base, region_off in Hr. rewrite Z.shiftl_mul_pow2 in Hr by lia.
unfold AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[[Hw|[Hw|Hw]]|[Hf [[Hw|[Hw|Hw]]|Hw]]]].
- clear - Hr Hw U0 U1 hSB1 hSB2 hSP S1 S2 Hc'. unfold KSTACK, kSpaceSize, kFreeArrayOffset, kPrimResvSize in *. lia.
- clear - Hr Hw U0 U1 hSB1 hSB2 hTP D1 D2 D3 D4 Hc'. unfold kSpaceSize, kFreeArrayOffset, kPrimResvSize, kThreadObjSize, t_cache in *. lia.
- unfold AFgk.SLOTv in Hw. clear - Hr Hw U0 U1 hSB1 hSB2 hTP D1 D2 D3 D4 K3 CNTP Hc'. unfold kSpaceSize, kFreeArrayOffset, kPrimResvSize, kThreadObjSize, t_cache in *. lia.
- clear - Hr Hw U0 U1 hSB1 hSB2 hTP D1 D2 D3 D4 Hc'. unfold kSpaceSize, kFreeArrayOffset, kPrimResvSize, kThreadObjSize, t_cache in *. lia.
- clear - Hr Hw U0 U1 D5 D6 D7 D8 Hc'. unfold kRegionInfoOff, kFreeArrayOffset in *. lia.
- clear - Hr Hw U0 U1 D5 D6 D7 D8 Hc'. unfold kRegionInfoOff, kFreeArrayOffset in *. lia.
- clear - Hr Hw U0 U1 D5 D6 D7 D8 Hc'. unfold kRegionInfoOff, kFreeArrayOffset in *. lia.
- unfold AFgk.DSTv, AFgk.FAv, AFgk.RBv in Hw. rewrite K7 in Hw. unfold kold, AFgk.Nv, AFgk.MAXv in *.
  destruct (Z.eq_dec c' c) as [->|NE].
  + clear - Hr Hw F0 A0 A1 R1. unfold kFreeArrayOffset in *. lia.
  + clear - Hr Hw F0 F10 U0 U1 NE Hcc Hc' K5 K6. unfold kFreeArrayOffset in *. lia.
Qed.
Lemma LEAF : (kcnt = MAXv -> 4 * (kold + Nv) <= kmf) ->
forall W' c', AFgk.at_RETK W ly regs mem md c off kcnt kold kmf W' c' -> cd_postR (tt, AFez.S' X c off) W' c'.
Proof.
intros NG W' c' HR.
destruct HR as (-> & regs' & mem' & mat & -> & CSP & CS & MEQ' & PRESW & VALS). cbv zeta in VALS. destruct VALS as (V1 & V2 & VF).
pose proof PREF as (Hi & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
assert (ROOM : 4 * (kold + (if kcnt =? AFgk.MAXv c then AFgk.Nv c else 0)) <= kmf).
{ pose proof reg_facts as (F0 & F1 & _). destruct (Z.eqb_spec kcnt (AFgk.MAXv c)) as [E|NE]; [exact (NG E) | lia]. }
pose proof (cr_step _ _ _ _ _ RD inst ly X W regs mem md c off mem' mat AR0 MOD (conj Hlo Hhi) ROOM MEQ' PRESW V1 V2 VF) as [STEP AOXS].
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (NOTW : forall a, 0 <= a < 2 ^ 64 -> ~ WINk a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hn. apply MEQ'. rewrite unsigned_lit_small by exact Ha. exact Hn. }
assert (SCR : forall a, WINk a -> ~ AOX ly X a -> ascratch B KSTACK_CF regs a).
{ intros a Hw NO. destruct (Z_lt_le_dec a (sp0 - 320)) as [L|L]; [|destruct (Z_lt_le_dec a sp0) as [L2|L2]].
  - exfalso. apply NO. apply WIN_owned; [exact Hw | lia].
  - left. unfold spZ. fold sp0. unfold KSTACK_CF. lia.
  - exfalso. apply NO. apply WIN_owned; [exact Hw | lia]. }
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ split; [exact STEP|]. split; [apply YG0f.layout_le_refl|]. split; [apply wle_refl|]. split; [|split; [|split]].
  - intros r Hr'. unfold acallee_saved in Hr'.
    assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct R as [->|R]; [exact CSP|]. apply CS. clear - R. unfold AFgk.SREGS.
    repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
  - apply same_io_l.
  - intros a Ha NO _ NS _. apply aview_same. apply NOTW; [exact Ha|]. intros Hw. exact (NS (SCR a Hw NO)).
  - intros a Ha. unfold spZ in Ha. fold sp0 in Ha. destruct (WIN_dec a) as [Hw|Hw].
    + exact (PRESW a Hw).
    + apply (apresent_same (w_H W) mem); [|apply HPRES; unfold spZ; fold sp0; exact Ha].
      apply NOTW; [|exact Hw]. pose proof HI as (_ & _ & _ & _ & hS1 & hS2 & _).
      clear - Ha Usp Hlo Hhi hS1 hS2. unfold spZ in Hlo, Hhi. fold sp0 in Hlo, Hhi. unfold KSTACK_CF, kHighMemBeg, kHighMemEnd in *. lia. }
split.
{ intros x NO _ NS _. apply MEQ'. intros Hw. exact (NS (SCR _ Hw NO)). }
split.
{ intros i Hii. try unfold w64. apply NOTW; [rewrite (ts_errno _ TB); unfold TFIB_ERRNO; lia | exact (errno_not_WIN i Hii)]. }
split.
{ apply (MemnormT.memnorm_frame tfibsegs (fun z => WINk z)); [|exact MEQ'].
  intros x Hw. cbv beta in Hw. apply win_zone_mn. destruct (WIN_zone _ Hw) as [Hz|[Hz|Hz]];
  [left; unfold KSTACK; lia | right; left; lia | right; right; exact Hz]. }
split.
{ intros a Ha Hu. apply aview_same. apply NOTW; [exact Ha | exact (puser_not_WIN a Hu)]. }
split.
{ intros a (c' & Hc' & Hr). exists c'. split; [exact Hc'|]. cbn [snd]. rewrite (alloc_S' c' ltac:(lia)). exact Hr. }
split; [exact S'_cinit_l | exact AOXS].
Qed.
Theorem arm_nogrow : (kcnt = MAXv -> 4 * (kold + Nv) <= kmf) ->
amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) cd_postS.
Proof.
intros NG. rewrite (model_step NG). cbn [amreal].
destruct junk_vals as (j80 & j88 & jst & HJ80 & HJ88 & HJST).
pose proof (FH_ok j80 j88 jst HJ80 HJ88 HJST NG) as FH.
unfold cfg_at, A_CDealloc. rewrite <- (wvb_self_l md) at 1.
eapply SRr_mono; [| intros W' c' _ HR; split; [exact (LEAF NG W' c' HR) | left; split; [exact NG | reflexivity]]].
destruct (Z_lt_le_dec kcnt MAXv) as [LT|GE].
- exact (AFgy.segK1 W ly regs mem md c off kcnt kold kmf j80 j88 jst (m_vm_materialized md) FH LT).
- apply (AFgz.segK2 W ly regs mem md c off kcnt kold kmf j80 j88 jst (m_vm_materialized md) FH).
  pose proof reg_facts as RFx. clear - RFx GE. unfold AFgk.MAXv in *. lia.
Qed.

Definition low_okq (a w : Z) : bool :=
((TFIB_IMG_LO <=? a) && (a + w <=? TFIB_IMG_END)) || ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).
Definition const_loc_okq (ce : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w ce)) in
match c_at ce with
| ANum a => low_okq a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okq (TFIB_TSD + o) w
| ATp o => low_okq (TFIB_TP + o) w
| AInst o => low_okq (TFIB_INST + o) w
| _ => false
end.
Lemma Tfib_const_locq : forallb const_loc_okq (Tfib_const ly) = true.
Proof. clear. vm_compute. reflexivity. Qed.
Lemma GEOL :
(ly_prim ly + kPrimResvSize <= T \/ T + kThreadObjSize <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_C ly \/ ly_C ly + 256 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_D ly \/ ly_D ly + 4096 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_prim ly) /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\
(T + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= T) /\
(ly_C ly + 256 <= ly_D ly \/ ly_D ly + 4096 <= ly_C ly) /\
(ly_C ly + 256 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_C ly) /\
(ly_D ly + 4096 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_D ly) /\
(4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) /\ (4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL).
Proof.
pose proof (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) as IC. pose proof (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) as ID.
cbn beta in IC, ID. cbn [fst snd] in IC, ID. unfold in_app in IC, ID.
assert (C12 : 4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) by (clear - IC; ceil; unfold zone3, TFIB_IMG_LO, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia).
assert (D12 : 4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL) by (clear - ID; ceil; unfold zone3, TFIB_IMG_LO, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia). clear IC ID.
pose proof (lo_disj ly LO) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & DC & DD & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [PD DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [TD DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [CD DC]. apply Forall_cons_iff in DC as [CSTK _]. apply Forall_cons_iff in DD as [DSTK _].
destruct C12 as [C1 C2]. destruct D12 as [D1 D2].
unfold zdisjoint in *. cbn [fst snd] in *. repeat match goal with G : _ /\ _ |- _ => destruct G as [? ?] end. splits; assumption.
Qed.
Lemma CONST_OUT : Forall (fun ce => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w ce)) -> ~ WINk (aeval B ly (c_at ce) + i) /\ 0 <= aeval B ly (c_at ce) + i < 2 ^ 64) (as_const B ly).
Proof.
assert (HTSD : ly_tsd ly = TFIB_TSD) by exact (proj2 (proj2 GEO)).
rewrite (ts_const _ TB). apply Forall_forall. intros ce Hce i Hi.
pose proof (proj1 (forallb_forall _ _) Tfib_const_locq ce Hce) as K. unfold const_loc_okq in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEOL as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((sp0 - 320 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINk a).
{ intros a Hn Hw. exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okq a (Z.max 1 (Z.of_nat (c_w ce))) = true -> ~ WINk (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L'. unfold low_okq in L'.
split; [apply ZN|]; clear - L' Hi hP1 hT1 hS1 S1; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, KSTACK, kThreadObjSize in *;
change (65536 / 8) with 8192 in *; change (6291456 / 8) with 786432 in *; lia. }
destruct (c_at ce); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [apply ZN|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
- split; [apply ZN|]; clear - K Hi C1 C2 S1 S2 G_PC G_TC G_CS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [apply ZN|]; clear - K Hi D1 D2 S1 S2 G_PD G_TD G_DS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, KSTACK in *; lia.
Qed.

Lemma WINX_WIN : forall a, DMcdGk.WINX ly regs c kcnt a -> WINk a.
Proof.
intros a Hx. unfold DMcdGk.WINX, DMcdGk.WRG in Hx. unfold AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG. fold sp0.
destruct Hx as [Hx|[Hx|[Hx|[Hf Hx]]]].
- left. exact Hx.
- right. left. left. exact Hx.
- right. left. right. right. exact Hx.
- right. right. split; [exact Hf|]. left. exact Hx.
Qed.
Lemma WINX_dec : forall a, DMcdGk.WINX ly regs c kcnt a \/ ~ DMcdGk.WINX ly regs c kcnt a.
Proof.
intros a. change (Decidable.decidable (DMcdGk.WINX ly regs c kcnt a)). unfold DMcdGk.WINX, DMcdGk.WRG.
repeat first [apply Decidable.dec_or | apply Decidable.dec_and | apply Z.eq_decidable | apply Z.le_decidable | apply Z.lt_decidable].
Qed.

Lemma img_cells_at : forall m', (forall x : word, ~ WINk (bv_unsigned x) -> m' x = mem x) ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) m')) (as_const B ly).
Proof.
intros m' Hm. pose proof img_cells as HC. pose proof CONST_OUT as CO.
apply Forall_forall. intros ce Hce.
eapply YG0q.cell_holds_agree; [exact (proj1 (Forall_forall _ _) HC ce Hce) |].
intros k Hk. destruct (proj1 (Forall_forall _ _) CO ce Hce k Hk) as [NW R].
apply aview_same. apply Hm. rewrite unsigned_lit_small by exact R. exact NW.
Qed.

Definition KG (X1 : astate) : astate :=
  YFfh.XK_push c off (upd_pc c (mkPC (pc_max (cache X c)) (YFfh.kkeep c X))
    (upd_reg c (mkRegion (rg_mapped_user (reg X1 c)) (rg_alloc_user (reg X1 c)) (rg_mapped_fa (reg X1 c))
      (fa_push_list (rg_free (reg X1 c)) (YFfh.kdrained c X)) (rg_holes (reg X1 c))) X1)).
Lemma Hfull_pm : kcnt = MAXv -> Z.of_nat (length (pc_chunks (cache X c))) = pc_max (cache X c).
Proof. intros E. pose proof reg_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PM & _). rewrite PM. exact E. Qed.
Lemma ibind_assoc_m {S A B0 C} : forall (t : itree S A) (f : A -> itree S B0) (g : B0 -> itree S C),
  ibind (ibind t f) g = ibind t (fun x => ibind (f x) g).
Proof.
induction t as [x | q s k IH | pc | e]; intros f g; cbn; try reflexivity.
f_equal. apply FunctionalExtensionality.functional_extensionality. intros z. apply IH.
Qed.

Lemma cd_grow_eq : kcnt = MAXv ->
  cache_dealloc c off X = ibind (ensure_free_array c (kold + Nv) true X) (fun '(_, X1) => IRet (tt, KG X1)).
Proof.
intros HF.
pose proof reg_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PM & _). pose proof class_facts as (_ & _ & K3 & _ & K5 & K6 & _).
assert (LK : length (YFfh.kdrained c X) = Z.to_nat Nv).
{ unfold YFfh.kdrained. cbv zeta. rewrite PM, length_skipn. change (AFgk.MAXv c / 2) with (AFgk.Nv c).
  unfold kcnt, AFgk.MAXv in *. clear - HF K5 K6. lia. }
unfold cache_dealloc, init_cache_if_needed, get_pc, set_pc, return_to_allocator, get_region, set_region.
unfold bind, get, ret, put, modify. cbn [ibind].
rewrite Hci. cbn [ibind]. fold (cache X c). rewrite (proj2 (Z.eqb_eq _ _) (Hfull_pm HF)). cbn [ibind]. fold (reg X c).
fold (YFfh.kdrained c X). rewrite LK, Z2Nat.id by (clear - K5; lia).
rewrite !ibind_assoc_m. f_equal. apply FunctionalExtensionality.functional_extensionality. intros [b X1]. cbn [ibind]. reflexivity.
Qed.
Lemma round_grow : kcnt = MAXv -> kmf < 4 * (kold + Nv) ->
  round_up (4 * (kold + Nv)) kFreeArrayMapSize = kmf + kFreeArrayMapSize.
Proof.
intros HF HG. pose proof reg_facts as (F0 & F1 & [F2 F3] & F4 & _). pose proof class_facts as (_ & _ & _ & _ & K5 & _).
unfold round_up. apply Z.mod_divide in F4 as [q Hq]; [|unfold kFreeArrayMapSize; lia]. unfold kFreeArrayMapSize in *.
rewrite <- (Z.div_unique (4 * (kold + Nv) + 262144 - 1) 262144 (q + 1) (4 * (kold + Nv) - 1 - kmf)).
- clear - Hq. lia.
- left. clear - Hq F1 HG K5. lia.
- clear - Hq. lia.
Qed.
Lemma tree_grow : kcnt = MAXv -> kmf < 4 * (kold + Nv) ->
  exists c0 old dl snap k g, cache_dealloc c off X = IAsk (KMapFreeArray c0 old dl) snap k /\
    aGranted g = true /\ k g = IRet (tt, SG).
Proof.
intros HF HG. pose proof reg_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11).
assert (MS : kmf + kFreeArrayMapSize <= kFreeArrayMax) by exact (F11 HG).
rewrite (cd_grow_eq HF). unfold ensure_free_array, get_region, bind, get, ret, mcheck, askz. cbn [ibind]. fold (reg X c).
pose proof (round_grow HF HG) as RG. unfold kmf in HG, MS, RG.
rewrite (proj2 (Z.leb_gt _ _) HG). cbn [ibind].
rewrite RG. rewrite (proj2 (Z.leb_le _ _) MS). cbn [ibind].
do 5 eexists. exists 1. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
Qed.
Lemma amreal_cd_grow : kcnt = MAXv -> forall W0 c0 (Q : unit * astate -> world tfibsegs -> config -> Prop),
  amreal tfibsegs (bind (ensure_free_array c (kold + Nv) true) (fun _ X1 => IRet (tt, KG X1)) X) W0 c0 Q ->
  amreal tfibsegs (cache_dealloc c off X) W0 c0 Q.
Proof.
intros HF W0 c0 Q H.
pose proof reg_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PM & _). pose proof class_facts as (_ & _ & K3 & _ & K5 & K6 & _).
assert (LK : length (YFfh.kdrained c X) = Z.to_nat Nv).
{ unfold YFfh.kdrained. cbv zeta. rewrite PM, length_skipn. change (AFgk.MAXv c / 2) with (AFgk.Nv c).
  unfold kcnt, AFgk.MAXv in *. clear - HF K5 K6. lia. }
unfold cache_dealloc, init_cache_if_needed, get_pc, set_pc, return_to_allocator, get_region, set_region.
unfold bind, get, ret, put, modify. cbn [ibind].
rewrite Hci. cbn [ibind]. fold (cache X c). rewrite (proj2 (Z.eqb_eq _ _) (Hfull_pm HF)). cbn [ibind]. fold (reg X c).
fold (YFfh.kdrained c X). rewrite LK, Z2Nat.id by (clear - K5; lia).
rewrite !ibind_assoc_m.
unfold bind in H.
eapply (YFfk.amreal_ibind_ext tfibsegs); [|exact H].
intros [b X1] W1 c1 H1. cbn [ibind] in H1 |- *. exact H1.
Qed.

Lemma byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v b,
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v -> a <= b < a + Z.of_nat n ->
  apresent H m b -> apresent H' m' b -> m (Z_to_bv 64 b) = m' (Z_to_bv 64 b).
Proof.
intros H H' m m' a n v b V V' Hb [Hh [x Hx]] [Hh' [y Hy]].
set (k := Z.to_nat (b - a)). assert (Ek : b = a + Z.of_nat k) by (unfold k; lia).
pose proof (V k ltac:(unfold k; lia)) as V1. pose proof (V' k ltac:(unfold k; lia)) as V2. rewrite <- Ek in V1, V2.
unfold mbyte, mrestrict in V1, V2. rewrite Hh, Hx in V1. rewrite Hh', Hy in V2. cbn in V1, V2. rewrite Hx, Hy. congruence.
Qed.
Lemma vm_move : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> H' (Z_to_bv 64 (a + Z.of_nat k)) = H (Z_to_bv 64 (a + Z.of_nat k)) /\
                           m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof. intros H H' m m' a n v HE Hv k Hk. destruct (HE k Hk) as [E1 E2]. rewrite <- (Hv k Hk). unfold mbyte, mrestrict. rewrite E1, E2. reflexivity. Qed.
Lemma aview_move : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  H' (Z_to_bv 64 a) = H (Z_to_bv 64 a) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview tfibsegs H' m' a = aview tfibsegs H m a.
Proof. intros H H' m m' a E1 E2. unfold aview, mbyte, mrestrict. rewrite E1, E2. reflexivity. Qed.
Lemma wvb_wvb : forall l l' a b (m : Model), with_vm_backing l a (with_vm_backing l' b m) = with_vm_backing l a m.
Proof. intros l l' a b [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_tr : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.

Definition WTb (a : Z) : bool :=
  ((sp0 - 320 <=? a) && (a <? sp0)) || ((PCv <=? a) && (a <? PCv + 4)) || ((SLOTv' <=? a) && (a <? SLOTv' + 4)) ||
  ((T + t_cache + 2576 <=? a) && (a <? T + t_cache + 2584)) || ((RGv <=? a) && (a <? RGv + 8)) ||
  ((RGv + 16 <=? a) && (a <? RGv + 24)) || ((RGv + 80 <=? a) && (a <? RGv + 88)) || ((DSTv' <=? a) && (a <? DSTv' + 4 * Nv)).
Lemma WTb_spec : kcnt = MAXv -> forall a, WTb a = true <-> WINk a.
Proof.
intros HF a. unfold WTb, AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG. fold sp0.
rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt. clear - HF. tauto.
Qed.
Lemma apresent_move : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  H' (Z_to_bv 64 a) = H (Z_to_bv 64 a) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> apresent H m a -> apresent H' m' a.
Proof. intros H H' m m' a E1 E2 [Hh [b Hb]]. split; [rewrite E1; exact Hh|]. exists b. rewrite E2. exact Hb. Qed.
Lemma WIN_parts : kcnt = MAXv -> forall a, ~ WINk a ->
  ~ (sp0 - 320 <= a < sp0) /\ ~ (PCv <= a < PCv + 4) /\ ~ (SLOTv' <= a < SLOTv' + 4) /\
  ~ (T + t_cache + 2576 <= a < T + t_cache + 2584) /\ ~ (RGv <= a < RGv + 8) /\ ~ (RGv + 16 <= a < RGv + 24) /\
  ~ (RGv + 80 <= a < RGv + 88) /\ ~ (DSTv' <= a < DSTv' + 4 * Nv).
Proof.
intros HF a N. unfold AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG in N. fold sp0 in N. clear - HF N. tauto.
Qed.
Section gr.
Variables (j80 j88 jst : Z).
Hypothesis HJ80 : 0 <= j80 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 80) 8 j80.
Hypothesis HJ88 : 0 <= j88 < 2 ^ 64 /\ val_mem tfibsegs m0 (RGv + 88) 8 j88.
Hypothesis HJST : 0 <= jst < 2 ^ 64 /\ val_mem tfibsegs m0 (T + t_cache + 2576) 8 jst.

Lemma EFA_PRE : kcnt = MAXv -> kmf < 4 * (kold + Nv) ->
forall c9, DMcdGI.at_EFA W ly regs mem md c off kcnt kold kmf j80 j88 jst c9 ->
DMcdGI.efa_mach W ly regs md c kold kmf j80 j88 jst c9 ->
forall regs9 mem9 md9, c9 = cfg_at tfibsegs FGsN.A_EFA regs9 mem9 md9 ->
FGtN.efa_pre_lk B ly X W regs9 mem9 md9 c (kold + Nv) j80 j88 jst kold (rg_alloc_user (reg X c)) (rg_mapped_user (reg X c)).
Proof.
intros HF HG c9 AT MACH regs9 mem9 md9 E9. subst c9.
destruct AT as (ms9 & mat9 & E & Hc9 & _ & _ & MQ).
unfold cfg_at in Hc9. injection Hc9; intros; subst.
destruct MACH as (regs9' & mem9' & mat9' & Hc9' & RA & SP & TP & A0 & A1 & A2 & A3 & PW & V0 & V16 & V24 & V80 & V88 & VPC & VPC8 & VST).
unfold cfg_at in Hc9'. injection Hc9'; intros; subst regs9' mem9'.
cbn [ms_mem mkst] in MQ.
pose proof PREF as (_ & _ & _ & Hal & Hlo & Hhi & HPRES & _). unfold spZ in Hal, Hlo, Hhi, HPRES. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSB1 & hSB2 & _ & hTP & hTS & hPS & _).
destruct hT1 as (hT0 & _ & hTz).
pose proof derived as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _ & D16 & D17).
pose proof reg_facts as (F0 & F1 & [F2 F3] & F4 & _ & _ & _ & _ & _ & F10 & F11).
pose proof class_facts as (K1 & _ & K3 & _ & K5 & K6 & K7). pose proof CNTP_range as CNTP. pose proof Hc as Hcc.
pose proof HJ80 as [J80 _]. pose proof HJ88 as [J88 _]. pose proof HJST as [JST _].
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CEIL.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
unfold kmf in *.
assert (NW : forall x : word, ~ WINk (bv_unsigned x) -> mem9 x = mem x).
{ intros x Hx. apply MQ. intros Hw. exact (Hx (WINX_WIN _ Hw)). }
assert (FRM : forall a, 0 <= a < 2 ^ 64 -> ~ WINk a -> mem9 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hn. apply NW. rewrite unsigned_lit_small by exact Ha. exact Hn. }
assert (PRES : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem a -> apresent (w_H W) mem9 a).
{ intros a Ha HP. destruct (WINX_dec a) as [Hx|Hx].
  - apply PW. unfold DMcdGk.WINX, DMcdGk.WRG in Hx.
    destruct Hx as [Q|[Q|[Q|[_ [Q|[Q|Q]]]]]].
    + left. exact Q.
    + do 4 right. left. exact Q.
    + do 5 right. clear - Q. unfold t_cache in Q. lia.
    + right. left. exact Q.
    + do 2 right. left. exact Q.
    + do 3 right. left. exact Q.
  - apply (apresent_same _ mem); [|exact HP]. apply MQ. rewrite unsigned_lit_small by exact Ha. exact Hx. }
assert (VK : forall a n v, (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ WINk (a + k)) ->
  val_mem tfibsegs m0 a n v -> val_mem tfibsegs (mrestrict (w_H W) mem9) a n v).
{ intros a n v Hk Hv. apply (val_mem_frame _ mem); [|exact Hv]. intros k Hk'.
  destruct (Hk (Z.of_nat k) ltac:(clear - Hk'; lia)) as [R N]. apply FRM; assumption. }

assert (WK : forall a, WINk a -> (sp0 - 320 <= a < sp0) \/ (PCv <= a < PCv + 4) \/ (PCv + 16 <= a < PCv + 16 + 4 * MAXv) \/
  (T + t_cache + 2576 <= a < T + t_cache + 2584) \/ (RGv <= a < RGv + 8) \/ (RGv + 16 <= a < RGv + 24) \/
  (RGv + 80 <= a < RGv + 88) \/ (FAv + 4 * kold <= a < FAv + 4 * kold + 4 * Nv)).
{ intros a Hw. unfold AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG in Hw. fold sp0 in Hw.
  destruct Hw as [Q|[[Q|[Q|Q]]|[_ [[Q|[Q|Q]]|Q]]]].
  - left. exact Q.
  - right. left. exact Q.
  - do 2 right. left. unfold AFgk.SLOTv in Q. clear - Q CNTP. lia.
  - do 3 right. left. exact Q.
  - do 4 right. left. exact Q.
  - do 5 right. left. exact Q.
  - do 6 right. left. exact Q.
  - do 7 right. unfold AFgk.DSTv in Q. exact Q. }
assert (OFF : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 320 <= a < sp0) -> ~ (PCv <= a < PCv + 4) ->
  ~ (PCv + 16 <= a < PCv + 16 + 4 * MAXv) -> ~ (T + t_cache + 2576 <= a < T + t_cache + 2584) -> ~ (RGv <= a < RGv + 8) ->
  ~ (RGv + 16 <= a < RGv + 24) -> ~ (RGv + 80 <= a < RGv + 88) -> ~ (FAv + 4 * kold <= a < FAv + 4 * kold + 4 * Nv) ->
  0 <= a < 2 ^ 64 /\ ~ WINk a).
{ intros a R N1 N2 N3 N4 N5 N6 N7 N8. split; [exact R|]. intros Hw.
  destruct (WK a Hw) as [Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]]; contradiction. }
assert (NV8 : Nv <= 8) by (clear - K5; lia).
assert (MSG : rg_mapped_fa (reg X c) + kFreeArrayMapSize <= kFreeArrayMax) by exact (F11 HG).
assert (DSTE : FAv + 4 * kold + 4 * Nv <= SB + 31 * 2 ^ 32).
{ clear - D12 D14 F1 MSG NV8. unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize in *. lia. }
assert (FA0 : SB + 2 ^ 32 <= FAv) by (clear - D12 D13; unfold kFreeArrayOffset in *; lia).

assert (RGO : forall o, (8 <= o < 16) \/ (24 <= o < 80) -> 0 <= RGv + o < 2 ^ 64 /\ ~ WINk (RGv + o)).
{ intros o Ho. apply OFF.
  - clear - Ho D5 D6 D7 D8 D9 D10 CEIL. unfold kHighMemBeg, kRegionInfoOff in *. lia.
  - clear - Ho D5 D6 D7 D8 D16 hSB1 hSB2 hPS Hlo Hhi Usp. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, KSTACK_CF in *. lia.
  - clear - Ho D1 D2 D3 D5 D6 D7 D8 hSB1 hSB2 hTP. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kThreadObjSize, t_cache in *. lia.
  - clear - Ho K3 D1 D2 D3 D4 D5 D6 D7 D8 hSB1 hSB2 hTP. unfold AFgk.MAXv in *. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kThreadObjSize, t_cache in *. lia.
  - clear - Ho D1 D2 D3 D4 D5 D6 D7 D8 hSB1 hSB2 hTP. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kThreadObjSize, t_cache in *. lia.
  - clear - Ho. lia.
  - clear - Ho. lia.
  - clear - Ho. lia.
  - clear - Ho D5 D7 DSTE. unfold kRegionInfoOff in *. lia. }

assert (TO : forall a, (PCv + 4 <= a < PCv + 16) \/ (T + 2800 <= a < T + kThreadObjSize) -> 0 <= a < 2 ^ 64 /\ ~ WINk a).
{ intros a Ha. apply OFF.
  - clear - Ha hT0 hT2 D1 D2 CEIL. unfold kThreadObjSize in *. lia.
  - clear - Ha hTS Hlo Hhi D1 D2 D3 Usp. unfold kThreadObjSize, KSTACK_CF, t_cache in *. lia.
  - clear - Ha D4. unfold t_cache in *. lia.
  - clear - Ha K3 D4. unfold AFgk.MAXv in *. unfold t_cache in *. lia.
  - clear - Ha D4. unfold t_cache in *. lia.
  - clear - Ha hTP D1 D2 D3 D5 D6 D7 D8 hSB1 hSB2. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kThreadObjSize, t_cache in *. lia.
  - clear - Ha hTP D1 D2 D3 D5 D6 D7 D8 hSB1 hSB2. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kThreadObjSize, t_cache in *. lia.
  - clear - Ha hTP D1 D2 D3 D5 D6 D7 D8 hSB1 hSB2. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kThreadObjSize, t_cache in *. lia.
  - clear - Ha hTP D1 D2 D3 FA0 DSTE F0 NV8 hSB1 hSB2. unfold kSpaceSize, kPrimResvSize, kThreadObjSize, t_cache in *. lia. }
assert (ERG : AFk5.RGv ly c = RGv) by (clear; unfold AFk5.RGv, AFgk.RGv, AFgk.RIv; lia).
assert (EPr : AFk5.Pr ly c = PCv) by reflexivity.
assert (ERB : AFk5.RBv ly c = RBv) by (clear - K7; unfold AFk5.RBv, AFgk.RBv; rewrite K7; lia).
assert (SP9 : bv_unsigned (getr regs9 2) = sp0 - 240).
{ rewrite SP. apply unsigned_lit_small. clear - Usp Hlo hS1. unfold KSTACK_CF, kHighMemBeg in *. lia. }
pose proof region_vals as (R0 & R8 & R16 & R24 & R32 & R40 & R48 & R56).
pose proof cache_vals as (C1 & C2 & C3).
unfold FGtN.efa_pre_lk. rewrite ERG, EPr, ERB, SP9.
split; [exact IMG|]. split; [exact LO|]. split; [exact TB|]. split; [exact (proj2 (proj2 GEO))|].
split. { apply img_cells_at. exact NW. }
split; [clear - Hcc; lia|].
split. { clear - F0 F10 K5. unfold AFgk.Nv, AFgk.MAXv in *. lia. }
split; [split; [clear - F2 F3; lia | exact F4]|].
split. { clear - F1 NV8. unfold kFreeArrayMapSize. lia. }
split. { rewrite RA. vm_compute. reflexivity. }
split; [exact TP|]. split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
split. { clear - Hal Hlo Hhi. unfold RSTACK, KSTACK_CF in *. split; [lia|]. split; [lia|].
  apply Z.mod_divide in Hal as [q Hq]; [|lia]. apply Z.mod_divide; [lia|]. exists (q - 15). lia. }
split. { intros a Ha. apply PRES; [clear - Ha Usp Hlo hS1; unfold RSTACK, KSTACK_CF, kHighMemBeg in *; lia|]. apply HPRES. clear - Ha. unfold RSTACK, KSTACK_CF in *. lia. }
split.
{ intros a Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  - apply PRES; [clear - Ha D7 D8 D9 D10 CEIL; unfold kHighMemBeg in *; lia|]. apply rinfo_present. exact Ha.
  - apply PRES; [clear - Ha D1 D2 hT2 CEIL; unfold kThreadObjSize in *; lia|]. apply thread_present. clear - Ha D1 D2 D3. unfold kThreadObjSize, t_cache in *. lia.
  - apply PRES; [clear - Ha hT0 hT2 CEIL; unfold kThreadObjSize in *; lia|]. apply thread_present. clear - Ha. unfold kThreadObjSize in *. lia.
  - apply PRES; [clear - Ha hT0 hT2 CEIL; unfold kThreadObjSize in *; lia|]. apply thread_present. clear - Ha. unfold kThreadObjSize in *. lia. }
split; [exact V24|].
split.
{ destruct (word_of_present (T + 2872)) as (w1 & Q1 & W1v); [intros i Hi; apply thread_present; clear - Hi; unfold kThreadObjSize; lia|].
  destruct (word_of_present (T + 2880)) as (w2 & Q2 & W2v); [intros i Hi; apply thread_present; clear - Hi; unfold kThreadObjSize; lia|].
  exists w1, w2. split; [exact Q1|]. split; [exact Q2|]. split.
  - apply VK; [|exact W1v]. intros k Hk. cbn in Hk. apply TO. right. clear - Hk. unfold kThreadObjSize. lia.
  - apply VK; [|exact W2v]. intros k Hk. cbn in Hk. apply TO. right. clear - Hk. unfold kThreadObjSize. lia. }
split; [exact V0|].
split; [split; [exact J80 | exact V80]|].
split; [split; [exact J88 | exact V88]|].
split; [rewrite Z.add_0_r; exact VPC|].
split; [exact VPC8|].
split; [split; [exact JST | exact VST]|].
split; [split; [exact F0 | exact F1]|].
split; [exact (cr_user _ _ _ _ _ RD _ _ _ _ _ _ c AR0 ltac:(clear - Hcc; lia))|].
split. { apply VK; [|exact R8]. intros k Hk. cbn in Hk. rewrite <- Z.add_assoc. apply RGO. clear - Hk. lia. }
split; [exact V16|].
split. { apply VK; [|exact R32]. intros k Hk. cbn in Hk. rewrite <- Z.add_assoc. apply RGO. clear - Hk. lia. }
split. { apply VK; [|exact R40]. intros k Hk. cbn in Hk. rewrite <- Z.add_assoc. apply RGO. clear - Hk. lia. }
split. { apply VK; [|exact R48]. intros k Hk. cbn in Hk. rewrite <- Z.add_assoc. apply RGO. clear - Hk. lia. }
split. { apply VK; [|exact R56]. intros k Hk. cbn in Hk. rewrite <- Z.add_assoc. apply RGO. clear - Hk. lia. }
split. { destruct (byte_of_present (RGv + 68) ltac:(apply rinfo_present; clear; lia)) as (v68 & V68r & V68).
  exists v68. split; [exact V68r|]. apply VK; [|exact V68]. intros k Hk. cbn in Hk. rewrite <- Z.add_assoc. apply RGO. clear - Hk. lia. }
split. { apply VK; [|exact C2]. intros k Hk. cbn in Hk. apply TO. left. clear - Hk. lia. }
intros Hgr.
assert (MS : rg_mapped_fa (reg X c) + kFreeArrayMapSize <= kFreeArrayMax) by (apply F11; clear - Hgr; unfold AFgk.Nv, AFgk.MAXv in *; lia).
split; [exact MS|].
assert (G5 : eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md)).
{ apply BUDG. clear - Hgr. unfold AFgk.Nv, AFgk.MAXv in *. exact Hgr. }
destruct (cr_grow _ _ _ _ _ RD _ _ _ _ _ _ c AR0 ltac:(clear - Hcc; lia) MS G5) as (G1 & G2 & G3 & G4 & G6).
rewrite m_vmmaps_wvb, eager_used_wvb.
split; [exact G1|]. split; [exact G2|].
split; [exact (amwf_same md _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) G3)|].
split; [exact G4|]. split; [exact G5|].
intros a Hs. pose proof (G6 a Hs) as G6a. unfold w64 in *.
assert (FAd : AFk5.FAv ly c = FAv) by (unfold AFk5.FAv, AFgk.FAv; rewrite ERB; reflexivity).
unfold AFkn.SHR, AFk5.SHBv in Hs. rewrite FAd in Hs.
assert (SH1 : SB + 2 ^ 32 <= FAv + rg_mapped_fa (reg X c) <= SB + 31 * 2 ^ 32).
{ clear - FA0 D12 D14 F2 F3. unfold kFreeArrayOffset, kFreeArrayMax in *. lia. }
assert (SH0 : 0 <= (FAv + rg_mapped_fa (reg X c)) / 8) by (apply Z.div_pos; clear - SH1 D16; unfold kHighMemBeg in *; lia).
assert (SH2 : (FAv + rg_mapped_fa (reg X c)) / 8 < 0x0fffffff0000).
{ apply Z.div_lt_upper_bound; [clear; lia|]. clear - SH1 D17 CEIL. unfold kSpaceSize in *. lia. }
assert (Lo : 0x7fff8000 <= a /\ a < kHighMemBeg) by (clear - Hs SH0 SH2; unfold kHighMemBeg; lia).
rewrite FRM; [exact G6a| clear - Lo; unfold kHighMemBeg in *; lia |].
assert (TL : T + kThreadObjSize <= a \/ a < T).
{ clear - Lo hTz. unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia. }
apply OFF.
- clear - Lo. unfold kHighMemBeg in *. lia.
- clear - Lo Hlo hS1. unfold KSTACK_CF in *. lia.
- clear - TL D1 D2 D3. unfold kThreadObjSize, t_cache in *. lia.
- clear - TL K3 D1 D2 D3 D4. unfold AFgk.MAXv in *. unfold kThreadObjSize, t_cache in *. lia.
- clear - TL. unfold kThreadObjSize, t_cache in *. lia.
- clear - Lo D5 D7 D16. unfold kRegionInfoOff in *. lia.
- clear - Lo D5 D7 D16. unfold kRegionInfoOff in *. lia.
- clear - Lo D5 D7 D16. unfold kRegionInfoOff in *. lia.
- clear - Lo FA0 D16 F0. unfold kHighMemBeg in *. lia.
Qed.

Lemma LEAFG : kcnt = MAXv -> kmf < 4 * (kold + Nv) ->
forall c9, DMcdGI.at_EFA W ly regs mem md c off kcnt kold kmf j80 j88 jst c9 ->
DMcdGI.efa_mach W ly regs md c kold kmf j80 j88 jst c9 ->
forall regs9 mem9 md9, c9 = cfg_at tfibsegs FGsN.A_EFA regs9 mem9 md9 ->
forall r W3 c3, FGtN.efa_leafT_lk ly X W regs9 mem9 md9 c (kold + Nv) j80 j88 jst kold (rg_alloc_user (reg X c)) (rg_mapped_user (reg X c)) r W3 c3 ->
forall W' c', DMcdGI.at_RETKG W ly regs mem c off kcnt kold W3 (cfg_model c3) (ms_mem (cfg_ms c3)) (rg_mapped_fa (reg (snd r) c)) W' c' ->
cd_postR (tt, KG (snd r)) W' c' /\ KG (snd r) = SG.
Proof.
intros HF HG c9 AT MACH regs9 mem9 md9 E9 r W3 c3 LEAF W' c' RET. subst c9.
destruct AT as (ms9 & mat9 & E & Hc9 & _ & _ & MQ).
unfold cfg_at in Hc9. injection Hc9; intros; subst.
destruct MACH as (regs9' & mem9' & mat9' & Hc9' & _ & SP & _ & _ & _ & _ & _ & PW & _).
unfold cfg_at in Hc9'. injection Hc9'; intros; subst regs9' mem9'.
cbn [ms_mem mkst] in MQ.
pose proof PREF as (_ & _ & _ & Hal & Hlo & Hhi & HPRES & _). unfold spZ in Hal, Hlo, Hhi, HPRES. fold sp0 in Hal, Hlo, Hhi, HPRES.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSB1 & hSB2 & _ & hTP & hTS & hPS & _).
pose proof hT1 as (hT0 & _ & hTz).
pose proof derived as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _ & D16 & D17).
pose proof reg_facts as (F0 & F1 & [F2 F3] & F4 & _ & _ & _ & _ & _ & F10 & F11).
pose proof class_facts as (K1 & _ & K3 & _ & K5 & K6 & K7). pose proof CNTP_range as CNTP. pose proof Hc as Hcc.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CEIL.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
unfold kmf in *.
assert (MSG : rg_mapped_fa (reg X c) + kFreeArrayMapSize <= kFreeArrayMax) by exact (F11 HG).
assert (SP9 : bv_unsigned (getr regs9 2) = sp0 - 240).
{ rewrite SP. apply unsigned_lit_small. clear - Usp Hlo hS1. unfold KSTACK_CF, kHighMemBeg in *. lia. }

unfold FGtN.efa_leafT_lk in LEAF. destruct LEAF as (j68 & J68e & LEAF). unfold FGcN.efa_leaf in LEAF.
destruct LEAF as [_ [(Hng & _ & _) | (_ & Hsnd & matN & W3' & Hwle & HwA & Hhsub & Hhid & Hsame & Hbytes & HAI & Hamwf & Hio & Heag & HRET)]].
{ exfalso. clear - Hng HG. unfold AFgk.Nv, AFgk.MAXv in *. lia. }
destruct HRET as (EW3 & regs3 & mem3 & mat3 & Hc3 & _ & _ & Hfr & Hstk & HP). subst W3.
destruct HP as [[[_ [Hgr Hshr]] Hfsh] [Hpmf Hlk]].
destruct Hlk as (Lk0 & Lk80 & Lk88 & Lkp & Lks & Lkt & Lkrg & Lk8 & Lk16 & Lk32 & Lk40 & Lk48 & Lk56 & Lk68 & Lkmax & Lkst).
rewrite Hc3 in RET. cbn [cfg_model cfg_ms ms_mem mkst] in RET.
destruct RET as (-> & regs' & mem' & mat' & Hc' & Rsp & Rcs & Rfr & Rpres & RV).
cbv zeta in RV. destruct RV as (RPC & RSLOT & RRG0 & RRG16 & RRG24 & RDST).

set (md2 := YG0b.grant_md false AFkn.FL50 (w64 (AFk5.FAv ly c + rg_mapped_fa (reg X c))) (w64 kUserMapSize) (with_vm_backing (m_vm_lazy md) matN md)).
match type of HAI with AI _ _ _ ?M => assert (EMD : M = md2) by (unfold FGcN.mdG, md2; rewrite m_vm_lazy_wvb, wvb_wvb; reflexivity); rewrite EMD in * end.
rewrite eager_used_wvb in Heag.

assert (ERG : AFk5.RGv ly c = RGv) by (clear; unfold AFk5.RGv, AFgk.RGv, AFgk.RIv; lia).
assert (EPr : AFk5.Pr ly c = PCv) by reflexivity.
assert (FAd : AFk5.FAv ly c = FAv) by (unfold AFk5.FAv, AFgk.FAv, AFk5.RBv, AFgk.RBv; rewrite K7; reflexivity).
rewrite ?ERG, ?EPr in *.
assert (NV8 : Nv <= 8) by (clear - K5; lia).
assert (FA0 : SB + 2 ^ 32 <= FAv) by (clear - D12 D13; unfold kFreeArrayOffset in *; lia).
assert (SH1 : SB + 2 ^ 32 <= AFk5.FAv ly c + rg_mapped_fa (reg X c) <= SB + 31 * 2 ^ 32).
{ rewrite FAd. clear - FA0 D12 D14 F2 F3. unfold kFreeArrayOffset, kFreeArrayMax in *. lia. }
assert (SH0 : 0 <= (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8) by (apply Z.div_pos; clear - SH1 D16; unfold kHighMemBeg in *; lia).
assert (SH2 : (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8 < 0x0fffffff0000).
{ apply Z.div_lt_upper_bound; [clear; lia|]. clear - SH1 D17 CEIL. unfold kSpaceSize in *. lia. }
assert (SHlo : forall a, AFkn.SHR (AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8) a -> 0x7fff8000 <= a < kHighMemBeg).
{ intros a Ha. unfold AFkn.SHR, AFk5.SHBv in Ha. clear - Ha SH0 SH2. unfold kHighMemBeg. lia. }
pose proof region_vals as (R0_ & R8_ & R16_ & R24_ & R32_ & R40_ & R48_ & R56_).
pose proof cache_vals as (C1_ & C2_ & C3_).

pose (WG1 := fun a => (sp0 - 240 - RSTACK <= a < sp0) \/ (RGv + 24 <= a < RGv + 32) \/ (RGv + 64 <= a < RGv + 68) \/
  (RGv + 69 <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) \/
  AFkn.RANGE (AFk5.FAv ly c + rg_mapped_fa (reg X c)) a \/ AFkn.SHR (AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8) a).
pose (WG1b := fun a => ((sp0 - 240 - RSTACK <=? a) && (a <? sp0)) || ((RGv + 24 <=? a) && (a <? RGv + 32)) ||
  ((RGv + 64 <=? a) && (a <? RGv + 68)) || ((RGv + 69 <=? a) && (a <? RGv + 128)) || ((T + 2768 <=? a) && (a <? T + 2800)) ||
  ((T + 2872 <=? a) && (a <? T + 2888)) ||
  ((AFk5.FAv ly c + rg_mapped_fa (reg X c) <=? a) && (a <? AFk5.FAv ly c + rg_mapped_fa (reg X c) + kUserMapSize)) ||
  ((AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8 <=? a) && (a <? AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8 + 32768))).
assert (WG1b_spec : forall a, WG1b a = true <-> WG1 a).
{ intros a. unfold WG1b, WG1, AFkn.RANGE, AFkn.SHR. rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt. tauto. }

pose proof Hfr as Hfr'. unfold FGcN.XG, AFk5.WINR0, AFk5.W_FSH in Hfr'. rewrite SP9, ?ERG, ?EPr in Hfr'.

assert (X3 : forall a, 0 <= a < 2 ^ 64 -> ~ WINk a -> ~ WG1 a -> mem3 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha N1 N2.
  destruct (WIN_parts HF a N1) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  assert (N2' : ~ (sp0 - 240 - RSTACK <= a < sp0) /\ ~ (RGv + 24 <= a < RGv + 32) /\ ~ (RGv + 64 <= a < RGv + 68) /\
    ~ (RGv + 69 <= a < RGv + 128) /\ ~ (T + 2768 <= a < T + 2800) /\ ~ (T + 2872 <= a < T + 2888) /\
    ~ AFkn.RANGE (AFk5.FAv ly c + rg_mapped_fa (reg X c)) a /\ ~ AFkn.SHR (AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8) a).
  { unfold WG1 in N2. clear - N2. tauto. }
  destruct N2' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). unfold AFkn.RANGE, AFkn.SHR in G7, G8.
  assert (CD : (PCv + 4 <= a < PCv + 16) \/ (RGv + 8 <= a < RGv + 16) \/ (RGv + 32 <= a < RGv + 64) \/ (RGv + 68 <= a < RGv + 69) \/
    ~ ((PCv + 4 <= a < PCv + 16) \/ (RGv + 8 <= a < RGv + 16) \/ (RGv + 32 <= a < RGv + 64) \/ (RGv + 68 <= a < RGv + 69))) by (clear; lia).
  assert (TP : forall b, T <= b < T + kThreadObjSize -> off_img b) by (intros b Hb; exact (zone3_off_img _ _ b hT1 Hb)).
  destruct CD as [Q|[Q|[Q|[Q|Q]]]].
  - destruct (Z_lt_le_dec a (PCv + 8)) as [L|L].
    + symmetry. eapply (byte_eq (w_H W) (w_H W3') mem mem3 (PCv + 4) 4 MAXv a); [exact C2_ | exact Lkmax | cbn; clear - Q L; lia | | ].
      * apply thread_present. clear - Q D1 D2 D3. unfold kThreadObjSize, t_cache in *. lia.
      * apply (DMcdGWb.val_mem_apresent _ _ (PCv + 4) 4 _ Lkmax); [intros b Hb; apply TP; cbn in Hb; clear - Hb D1 D2 D3; unfold kThreadObjSize, t_cache in *; lia | cbn; clear - Q L; lia].
    + symmetry. eapply (byte_eq (w_H W) (w_H W3') mem mem3 (PCv + 8) 8 SZv a); [exact C3_ | exact Lks | cbn; clear - Q L; lia | | ].
      * apply thread_present. clear - Q D1 D2 D3. unfold kThreadObjSize, t_cache in *. lia.
      * apply (DMcdGWb.val_mem_apresent _ _ (PCv + 8) 8 _ Lks); [intros b Hb; apply TP; cbn in Hb; clear - Hb D1 D2 D3; unfold kThreadObjSize, t_cache in *; lia | cbn; clear - Q L; lia].
  - symmetry. eapply (byte_eq (w_H W) (w_H W3') mem mem3 (RGv + 8) 8 0 a); [exact R8_ | exact Lk8 | cbn; clear - Q; lia | apply rinfo_present; clear - Q; lia | apply Lkrg; clear - Q; lia].
  - destruct (Z_lt_le_dec a (RGv + 40)) as [L1|L1]; [|destruct (Z_lt_le_dec a (RGv + 48)) as [L2|L2]; [|destruct (Z_lt_le_dec a (RGv + 56)) as [L3|L3]]].
    + symmetry. eapply (byte_eq (w_H W) (w_H W3') mem mem3 (RGv + 32) 8 _ a); [exact R32_ | exact Lk32 | cbn; clear - Q L1; lia | apply rinfo_present; clear - Q; lia | apply Lkrg; clear - Q; lia].
    + symmetry. eapply (byte_eq (w_H W) (w_H W3') mem mem3 (RGv + 40) 8 0 a); [exact R40_ | exact Lk40 | cbn; clear - L1 L2; lia | apply rinfo_present; clear - Q; lia | apply Lkrg; clear - Q; lia].
    + symmetry. eapply (byte_eq (w_H W) (w_H W3') mem mem3 (RGv + 48) 8 _ a); [exact R48_ | exact Lk48 | cbn; clear - L2 L3; lia | apply rinfo_present; clear - Q; lia | apply Lkrg; clear - Q; lia].
    + symmetry. eapply (byte_eq (w_H W) (w_H W3') mem mem3 (RGv + 56) 8 0 a); [exact R56_ | exact Lk56 | cbn; clear - Q L3; lia | apply rinfo_present; clear - Q; lia | apply Lkrg; clear - Q; lia].
  -
    assert (V68 : val_mem tfibsegs (mrestrict (w_H W) mem) (RGv + 68) 1 j68).
    { apply (val_mem_frame _ mem9); [|exact J68e]. intros k Hk.
      replace (RGv + 68 + Z.of_nat k) with a by (clear - Q Hk; lia).
      first [symmetry; apply MQ | apply MQ]; rewrite unsigned_lit_small by exact Ha; intros Hx; exact (N1 (WINX_WIN _ Hx)). }
    symmetry. eapply (byte_eq (w_H W) (w_H W3') mem mem3 (RGv + 68) 1 j68 a); [exact V68 | exact Lk68 | cbn; clear - Q; lia | apply rinfo_present; clear - Q; lia | apply Lkrg; clear - Q; lia].
  - rewrite Hfr'.
    + apply MQ. rewrite unsigned_lit_small by exact Ha. intros Hx. exact (N1 (WINX_WIN _ Hx)).
    + rewrite unsigned_lit_small by exact Ha. unfold AFkn.RANGE.
      intros [[[Z1|[Z2|[Z3|[Z4|Z5]]]]|Z6]|Z7].
      * apply G1. clear - Z1. unfold RSTACK in *. lia.
      * apply Q. clear - Z2 M2. lia.
      * apply Q. clear - Z3 M5 M6 M7 G2 G3 G4. lia.
      * apply G5. exact Z4.
      * apply G6. exact Z5.
      * apply G7. exact Z6.
      * apply G8. clear - Z7. unfold kFreeArrayMapSize in Z7. change (262144 / 8) with 32768 in Z7. exact Z7. }

assert (P3 : forall a, WG1 a -> apresent (w_H W3') mem3 a).
{ intros a Ha. destruct Ha as [Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]].
  - destruct (Z_lt_le_dec a (sp0 - 240)) as [L|L].
    + apply Hstk. rewrite SP9. clear - Q L. unfold RSTACK in *. lia.
    + assert (R : 0 <= a < 2 ^ 64) by (clear - Usp L Q Hlo hS1; unfold RSTACK, KSTACK_CF, kHighMemBeg in *; lia).
      assert (PW' : apresent (w_H W) mem9 a) by (apply PW; left; clear - Q L; lia).
      apply (apresent_move (w_H W) _ mem9); [ | | exact PW'].
      * destruct PW' as [Hh _]. rewrite (Hhid _ Hh), Hh. reflexivity.
      * apply Hfr'. rewrite unsigned_lit_small by exact R. unfold AFkn.RANGE.
        intros [[[Z1|[Z2|[Z3|[Z4|Z5]]]]|Z6]|Z7].
        -- clear - Z1 L. lia.
        -- clear - Z2 Q L D1 D2 D3 hTS Hlo Hhi. unfold kThreadObjSize, t_cache, RSTACK, KSTACK_CF in *. lia.
        -- clear - Z3 Q L D5 D7 D8 D16 hSB1 hSB2 hPS Hlo Hhi. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, RSTACK, KSTACK_CF in *. lia.
        -- clear - Z4 Q L hT0 hTS Hlo Hhi. unfold kThreadObjSize, RSTACK, KSTACK_CF in *. lia.
        -- clear - Z5 Q L hT0 hTS Hlo Hhi. unfold kThreadObjSize, RSTACK, KSTACK_CF in *. lia.
        -- clear - Z6 Q L SH1 FAd hSB1 hSB2 hPS Hlo Hhi. unfold kSpaceSize, kPrimResvSize, kUserMapSize, RSTACK, KSTACK_CF in *. lia.
        -- assert (Hs : 0x7fff8000 <= a < kHighMemBeg).
           { apply SHlo. unfold AFkn.SHR. clear - Z7. unfold kFreeArrayMapSize in Z7. change (262144 / 8) with 32768 in Z7. exact Z7. }
           clear - Hs Q L hS1 Hlo. unfold RSTACK, KSTACK_CF in *. lia.
  - apply Lkrg. clear - Q. lia.
  - apply Lkrg. clear - Q. lia.
  - apply Lkrg. clear - Q. lia.
  - apply Lkst. left. exact Q.
  - apply Lkst. right. exact Q.
  - exact (proj1 (Hgr a Q)).
  - exact (Hshr a Q). }

pose (mem1 := fun x : word => if WTb (bv_unsigned x) && negb (WG1b (bv_unsigned x)) then mem x else mem3 x).
assert (M1off : forall x : word, ~ WG1 (bv_unsigned x) -> mem1 x = mem x).
{ intros x Hx. unfold mem1. destruct (WTb (bv_unsigned x)) eqn:Eb.
  - assert (Eg : WG1b (bv_unsigned x) = false) by (destruct (WG1b (bv_unsigned x)) eqn:Eg'; [exfalso; exact (Hx (proj1 (WG1b_spec _) Eg')) | reflexivity]).
    rewrite Eg. reflexivity.
  - cbn [andb]. pose proof (X3 (bv_unsigned x) (bv_unsigned_in_range 64 x)) as Q. rewrite Z_to_bv_bv_unsigned in Q.
    apply Q; [|exact Hx]. intros Hw. apply (WTb_spec HF) in Hw. congruence. }
assert (M1lk : forall x : word, WG1 (bv_unsigned x) -> mem1 x = mem3 x).
{ intros x Hx. unfold mem1. rewrite (proj2 (WG1b_spec _) Hx). rewrite andb_false_r. reflexivity. }
assert (M1out : forall x : word, ~ WINk (bv_unsigned x) -> mem1 x = mem3 x).
{ intros x Hx. unfold mem1. destruct (WTb (bv_unsigned x)) eqn:Eb; [exfalso; exact (Hx (proj1 (WTb_spec HF _) Eb)) | reflexivity]. }
assert (M1pres : forall a, WG1 a -> apresent (w_H W3') mem1 a).
{ intros a Ha. destruct (P3 a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
  rewrite M1lk; [exact Hb|]. rewrite unsigned_lit_small; [exact Ha|].
  destruct Ha as [Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]].
  - clear - Q Usp Hlo hS1. unfold RSTACK, KSTACK_CF, kHighMemBeg in *. lia.
  - clear - Q D7 D8 D9 D10 CEIL. unfold kHighMemBeg in *. lia.
  - clear - Q D7 D8 D9 D10 CEIL. unfold kHighMemBeg in *. lia.
  - clear - Q D7 D8 D9 D10 CEIL. unfold kHighMemBeg in *. lia.
  - clear - Q hT0 hT2 CEIL. unfold kThreadObjSize in *. lia.
  - clear - Q hT0 hT2 CEIL. unfold kThreadObjSize in *. lia.
  - unfold AFkn.RANGE in Q. clear - Q SH1 D16 D17 CEIL. unfold kSpaceSize, kUserMapSize, kHighMemBeg in *. lia.
  - pose proof (SHlo a Q) as Hs. clear - Hs. unfold kHighMemBeg in *. lia. }

assert (RGn : forall o, 0 <= o < 24 -> 0 <= RGv + o < 2 ^ 64 /\ ~ WG1 (RGv + o) /\
  ~ AFkn.RANGE (AFk5.FAv ly c + rg_mapped_fa (reg X c)) (RGv + o) /\ ~ AFkn.SHR (AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8) (RGv + o)).
{ intros o Ho.
  assert (NR : ~ AFkn.RANGE (AFk5.FAv ly c + rg_mapped_fa (reg X c)) (RGv + o)).
  { unfold AFkn.RANGE. clear - Ho SH1 D5 D7. unfold kRegionInfoOff, kUserMapSize in *. lia. }
  assert (NS : ~ AFkn.SHR (AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8) (RGv + o)).
  { intros Hs. pose proof (SHlo _ Hs) as Q. clear - Q Ho D5 D7 D16. unfold kHighMemBeg, kRegionInfoOff in *. lia. }
  split; [clear - Ho D7 D8 D9 D10 CEIL; unfold kHighMemBeg in *; lia|]. split; [|split; assumption].
  unfold WG1. intros [Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]].
  - clear - Q Ho D5 D7 D8 D16 hSB1 hSB2 hPS Hlo Hhi. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, RSTACK, KSTACK_CF in *. lia.
  - clear - Q Ho. lia.
  - clear - Q Ho. lia.
  - clear - Q Ho. lia.
  - clear - Q Ho hTP D5 D7 D8 hSB1 hSB2. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kThreadObjSize in *. lia.
  - clear - Q Ho hTP D5 D7 D8 hSB1 hSB2. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize, kThreadObjSize in *. lia.
  - exact (NR Q).
  - exact (NS Q). }
assert (HSm : forall a, 0 <= a < 2 ^ 64 -> ~ AFkn.RANGE (AFk5.FAv ly c + rg_mapped_fa (reg X c)) a ->
  ~ AFkn.SHR (AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8) a -> w_H W3' (Z_to_bv 64 a) = w_H W (Z_to_bv 64 a)).
{ intros a Ha N1 N2. apply Hsame; rewrite unsigned_lit_small by exact Ha; assumption. }
unfold FGcN.P_mf in Hpmf. rewrite ERG in Hpmf.
assert (M1vals : let m1 := mrestrict (w_H W3') mem1 in
  val_mem tfibsegs m1 RGv 8 0 /\ val_mem tfibsegs m1 (RGv + 16) 8 kold /\
  val_mem tfibsegs m1 (RGv + 24) 8 (rg_mapped_fa (reg X c) + kFreeArrayMapSize) /\
  (forall a, AFkn.RANGE (AFk5.FAv ly c + rg_mapped_fa (reg X c)) a -> mem1 (w64 a) = Some (Z_to_bv 8 0)) /\
  (forall a, AFkn.SHR (AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8) a -> mem1 (w64 a) = Some (Z_to_bv 8 250))).
{ cbv zeta. split; [|split; [|split; [|split]]].
  - apply (vm_move (w_H W) _ mem); [|exact R0_]. intros k Hk. rewrite Z.add_0_r in *.
    destruct (RGn (Z.of_nat k) ltac:(clear - Hk; lia)) as (R & N1 & N2 & N3). split.
    + exact (HSm _ R N2 N3).
    + apply M1off. rewrite unsigned_lit_small by exact R. exact N1.
  - apply (vm_move (w_H W) _ mem); [|exact R16_]. intros k Hk. rewrite <- Z.add_assoc.
    destruct (RGn (16 + Z.of_nat k) ltac:(clear - Hk; lia)) as (R & N1 & N2 & N3). split.
    + exact (HSm _ R N2 N3).
    + apply M1off. rewrite unsigned_lit_small by exact R. exact N1.
  - apply (vm_move (w_H W3') _ mem3); [|exact Hpmf]. intros k Hk. split; [reflexivity|].
    apply M1lk. rewrite unsigned_lit_small by (clear - Hk D7 D8 D9 D10 CEIL; unfold kHighMemBeg in *; lia).
    unfold WG1. right. left. clear - Hk. lia.
  - intros a Ha. unfold w64. rewrite M1lk; [exact (proj2 (Hgr a Ha))|].
    rewrite unsigned_lit_small by (unfold AFkn.RANGE in Ha; clear - Ha SH1 D16 D17 CEIL; unfold kSpaceSize, kUserMapSize, kHighMemBeg in *; lia).
    unfold WG1. do 6 right. left. exact Ha.
  - intros a Ha. unfold w64.
    assert (R : 0 <= a < 2 ^ 64) by (pose proof (SHlo a Ha) as Q; clear - Q; unfold kHighMemBeg in *; lia).
    rewrite M1lk; [|rewrite unsigned_lit_small by exact R; unfold WG1; do 7 right; exact Ha].
    apply Hfsh. rewrite unsigned_lit_small by exact R. unfold AFkn.SHR in Ha. unfold kFreeArrayMapSize. change (262144 / 8) with 32768. exact Ha. }

pose (WT := fun a => (sp0 - 320 <= a < sp0) \/ (PCv <= a < PCv + 4) \/ (SLOTv' <= a < SLOTv' + 4) \/
  (T + t_cache + 2576 <= a < T + t_cache + 2584) \/ (RGv <= a < RGv + 8) \/ (RGv + 16 <= a < RGv + 24) \/
  (RGv + 80 <= a < RGv + 88) \/ (DSTv' <= a < DSTv' + 4 * Nv)).
assert (WT_WIN : forall a, WT a <-> WINk a).
{ intros a. unfold WT, AFgk.WIN, AFgk.WINF, AFgk.WINR, AFgk.WRG. fold sp0. clear - HF. tauto. }
assert (TOFF : forall x : word, ~ WT (bv_unsigned x) -> mem' x = mem1 x).
{ intros x Hx. rewrite M1out by (intros Hw; apply Hx; apply WT_WIN; exact Hw). apply Rfr. exact Hx. }
assert (TPRES : forall a, WT a -> apresent (w_H W3') mem' a) by (intros a Ha; apply Rpres; exact Ha).
pose proof (cr_growT _ _ _ _ _ RD inst ly X W regs mem md c off W3' mem1 mem' matN mat' AR0 MOD) as G.
cbv zeta in G.
assert (IO : same_io md md2) by exact (same_io_tr _ _ _ (same_io_l md mat9) Hio).
destruct (G (conj Hlo Hhi) HF HG Hwle HwA Hhsub Hhid Hsame Hbytes HAI Hamwf IO Heag M1off M1pres M1vals TOFF TPRES
  (conj RPC (conj RSLOT (conj RRG0 (conj RRG16 RDST))))) as (ARXf & AOXS & OWNG).

assert (MEQZ : forall a, 0 <= a < 2 ^ 64 -> ~ WINk a -> ~ WG1 a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha N1 N2. rewrite TOFF.
  - apply M1off. rewrite unsigned_lit_small by exact Ha. exact N2.
  - rewrite unsigned_lit_small by exact Ha. intros Hw. apply N1. apply WT_WIN. exact Hw. }
assert (MEQG : forall x : word, ~ WINk (bv_unsigned x) -> ~ WG1 (bv_unsigned x) -> mem' x = mem x).
{ intros x N1 N2. pose proof (MEQZ _ (bv_unsigned_in_range 64 x) N1 N2) as Q. rewrite Z_to_bv_bv_unsigned in Q. exact Q. }
assert (WG1d : forall a, WG1 a \/ ~ WG1 a).
{ intros a. destruct (WG1b a) eqn:Eg; [left; apply WG1b_spec; exact Eg | right; intros Hg; apply WG1b_spec in Hg; congruence]. }
assert (NRS : forall a, ~ WG1 a -> ~ AFkn.RANGE (AFk5.FAv ly c + rg_mapped_fa (reg X c)) a /\
  ~ AFkn.SHR (AFk5.SHBv + (AFk5.FAv ly c + rg_mapped_fa (reg X c)) / 8) a).
{ intros a Hn. split; intros Q; apply Hn; unfold WG1; tauto. }
assert (SCRG : forall a, (WINk a \/ WG1 a) -> ~ AOX ly X a -> ascratch B KSTACK_CF regs a).
{ intros a [Hw|Hg] NO.
  - destruct (Z_lt_le_dec a (sp0 - 320)) as [L|L]; [|destruct (Z_lt_le_dec a sp0) as [L2|L2]].
    + exfalso. apply NO. apply WIN_owned; [exact Hw | clear - L; lia].
    + left. unfold spZ. fold sp0. unfold KSTACK_CF. clear - L L2. lia.
    + exfalso. apply NO. apply WIN_owned; [exact Hw | clear - L2; lia].
  - destruct (Z_lt_le_dec a (sp0 - 240 - RSTACK)) as [L|L]; [|destruct (Z_lt_le_dec a sp0) as [L2|L2]].
    + exfalso. apply NO. apply OWNG; [exact Hg | clear - L; lia].
    + left. unfold spZ. fold sp0. unfold KSTACK_CF, RSTACK in *. clear - L L2. lia.
    + exfalso. apply NO. apply OWNG; [exact Hg | clear - L2; lia]. }
assert (NG : forall a, ~ AOX ly X a -> ~ ascratch B KSTACK_CF regs a -> ~ WINk a /\ ~ WG1 a).
{ intros a NO NS. split; intros Q; apply NS; apply SCRG; try assumption; [left | right]; exact Q. }
assert (ES : KG (snd r) = YFfh.XK_push c off (YFfh.XK_drain c (YG06.upd_reg c (FGcN.rgG (reg X c)) X))) by (rewrite Hsnd; reflexivity).
assert (AG : forall cq, 0 <= cq -> rg_alloc_user (reg (YFfh.XK_push c off (YFfh.XK_drain c (YG06.upd_reg c (FGcN.rgG (reg X c)) X))) cq) = rg_alloc_user (reg X cq)).
{ intros cq Hcq. unfold YFfh.XK_push, YFfh.XK_drain. cbv zeta. rewrite !reg_upd_pc.
  destruct (Z.eq_dec cq c) as [->|NE].
  - rewrite reg_upd_reg; [| clear - Hcc; lia | unfold YG06.upd_reg; cbn [st_regions set_regions]; rewrite zupd_length; exact HLr].
    cbn [rg_alloc_user]. rewrite reg_upd_reg; [reflexivity | clear - Hcc; lia | exact HLr].
  - rewrite reg_upd_reg_other; [| clear - Hcc; lia | exact Hcq | intros Q; exact (NE (eq_sym Q))].
    rewrite reg_upd_reg_other; [reflexivity | clear - Hcc; lia | exact Hcq | intros Q; exact (NE (eq_sym Q))]. }
rewrite ES. split; [|reflexivity].
unfold cd_postR. cbn [snd].
exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat' md2). split.
{ rewrite Hc'. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. rewrite m_vm_lazy_wvb, wvb_wvb. reflexivity. }
split.
{ split; [exact ARXf|]. split; [apply YG0f.layout_le_refl|]. split; [exact Hwle|]. split; [|split; [|split]].
  - intros rr Hr'. unfold acallee_saved in Hr'.
    assert (R : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    destruct R as [->|R]; [exact Rsp|]. apply Rcs. clear - R. unfold DMcdGk.SREGS.
    repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst rr; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
  - exact (same_io_tr _ _ _ IO (same_io_l md2 mat')).
  - intros a Ha NO _ NS _. destruct (NG a NO NS) as [N1 N2]. destruct (NRS a N2) as [N3 N4].
    apply aview_move; [exact (HSm a Ha N3 N4) | exact (MEQZ a Ha N1 N2)].
  - intros a Ha. unfold spZ in Ha. fold sp0 in Ha.
    assert (R : 0 <= a < 2 ^ 64) by (clear - Ha Usp Hlo hS1; unfold KSTACK_CF, kHighMemBeg in *; lia).
    destruct (WIN_dec a) as [Hw|Hw]; [apply TPRES; apply WT_WIN; exact Hw|].
    destruct (WG1d a) as [Hg|Hg].
    + apply (apresent_move (w_H W3') _ mem1); [reflexivity | | exact (M1pres a Hg)].
      apply TOFF. rewrite unsigned_lit_small by exact R. intros Hw'. apply Hw. apply WT_WIN. exact Hw'.
    + destruct (NRS a Hg) as [N3 N4].
      apply (apresent_move (w_H W) _ mem); [exact (HSm a R N3 N4) | exact (MEQZ a R Hw Hg) |].
      apply HPRES. exact Ha. }
split.
{ intros x NO _ NS _. destruct (NG _ NO NS) as [N1 N2]. exact (MEQG x N1 N2). }
split.
{ intros i Hii. try unfold w64.
  assert (RE : 0 <= as_errno B + i < 2 ^ 64) by (rewrite (ts_errno _ TB); unfold TFIB_ERRNO; lia).
  apply MEQZ; [exact RE | exact (errno_not_WIN i Hii) |].
  rewrite (ts_errno _ TB). unfold WG1, AFkn.RANGE, AFkn.SHR. intros [Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]].
  - clear - Q Hii Hlo hS1. unfold TFIB_ERRNO, RSTACK, KSTACK_CF, kHighMemBeg in *. lia.
  - clear - Q Hii D7 D9. unfold TFIB_ERRNO, kHighMemBeg in *. lia.
  - clear - Q Hii D7 D9. unfold TFIB_ERRNO, kHighMemBeg in *. lia.
  - clear - Q Hii D7 D9. unfold TFIB_ERRNO, kHighMemBeg in *. lia.
  - clear - Q Hii hTz hT0. unfold TFIB_ERRNO, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
  - clear - Q Hii hTz hT0. unfold TFIB_ERRNO, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in *. lia.
  - clear - Q Hii SH1 D16. unfold TFIB_ERRNO, kHighMemBeg in *. lia.
  - pose proof (SHlo _ Q) as Q'. clear - Q' Hii. unfold TFIB_ERRNO in *. lia. }
split.
{ apply (MemnormT.memnorm_frame tfibsegs (fun z => WINk z \/ WG1 z)).
  - intros x [Hw|Hg].
    + apply win_zone_mn. destruct (WIN_zone _ Hw) as [Hz|[Hz|Hz]];
      [left; unfold KSTACK; lia | right; left; lia | right; right; exact Hz].
    + pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
      destruct Hg as [Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]].
      * apply MemnormHitG.mn_safe_high. clear - Q Hlo Hhi hS1 hS2. unfold RSTACK, KSTACK_CF, kHighMemBeg, kHighMemEnd, kImgEnd, TASK_SIZE in *. lia.
      * apply win_zone_mn. right; right. clear - Q D5 D7 D8 hSB1 hSB2. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize in *. lia.
      * apply win_zone_mn. right; right. clear - Q D5 D7 D8 hSB1 hSB2. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize in *. lia.
      * apply win_zone_mn. right; right. clear - Q D5 D7 D8 hSB1 hSB2. unfold kSpaceSize, kRegionInfoOff, kPrimResvSize in *. lia.
      * apply win_zone_mn. right; left. clear - Q. unfold kThreadObjSize. lia.
      * apply win_zone_mn. right; left. clear - Q. unfold kThreadObjSize. lia.
      * apply win_zone_mn. right; right. unfold AFkn.RANGE in Q. clear - Q SH1 hSB1 hSB2. unfold kSpaceSize, kPrimResvSize, kUserMapSize in *. lia.
      * apply MemnormHitG.mn_safe_high. pose proof (SHlo _ Q) as Q'. clear - Q'. unfold kHighMemBeg, kImgEnd, TASK_SIZE in *. lia.
  - intros x Hn. apply MEQG; intros Q; apply Hn; [left | right]; exact Q. }
split.
{ intros a Ha Hu.
  assert (NW1 : ~ WG1 a).
  { destruct Hu as (cq & Hcq & Hr).
    pose proof (cr_user _ _ _ _ _ RD _ _ _ _ _ _ cq AR0 Hcq) as ([U0 U1'] & U1'' & _).
    unfold region_base, region_off in Hr. rewrite Z.shiftl_mul_pow2 in Hr by lia.
    unfold WG1, AFkn.RANGE. intros [Q|[Q|[Q|[Q|[Q|[Q|[Q|Q]]]]]]].
    - clear - Q Hr Hcq U1' U1'' U0 hSB1 hSB2 hPS Hlo Hhi D16. unfold kSpaceSize, kPrimResvSize, kFreeArrayOffset, RSTACK, KSTACK_CF in *. lia.
    - clear - Q Hr Hcq U1' U1'' U0 D5 D7. unfold kRegionInfoOff, kFreeArrayOffset in *. lia.
    - clear - Q Hr Hcq U1' U1'' U0 D5 D7. unfold kRegionInfoOff, kFreeArrayOffset in *. lia.
    - clear - Q Hr Hcq U1' U1'' U0 D5 D7. unfold kRegionInfoOff, kFreeArrayOffset in *. lia.
    - clear - Q Hr Hcq U1' U1'' U0 hTP hSB1 hSB2. unfold kSpaceSize, kPrimResvSize, kThreadObjSize, kFreeArrayOffset in *. lia.
    - clear - Q Hr Hcq U1' U1'' U0 hTP hSB1 hSB2. unfold kSpaceSize, kPrimResvSize, kThreadObjSize, kFreeArrayOffset in *. lia.
    - rewrite FAd in Q. unfold AFgk.FAv, AFgk.RBv in Q. rewrite K7 in Q.
      clear - Q Hr Hcq U1' U1'' U0 MSG Hcc F2. unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize in *.
      destruct (Z.eq_dec cq c) as [->|NE]; [lia|]. destruct (Z_lt_le_dec cq c); nia.
    - pose proof (SHlo _ Q) as Q'. clear - Q' Hr Hcq U0 U1' U1'' D16. unfold kHighMemBeg in *. lia. }
  destruct (NRS a NW1) as [N3 N4].
  apply aview_move; [exact (HSm a Ha N3 N4) | exact (MEQZ a Ha (puser_not_WIN a Hu) NW1)]. }
split.
{ intros a (cq & Hcq & Hr). exists cq. split; [exact Hcq|]. rewrite (AG cq ltac:(clear - Hcq; lia)). exact Hr. }
split; [exact Hci | exact AOXS].
Qed.
End gr.
Theorem arm_grow : kcnt = MAXv -> kmf < 4 * (kold + Nv) ->
amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) cd_postS.
Proof.
intros HF HG.
destruct junk_vals as (j80 & j88 & jst & HJ80 & HJ88 & HJST).
pose proof (FHG_ok j80 j88 jst HJ80 HJ88 HJST) as FHG.
apply (amreal_cd_grow HF).
unfold cfg_at at 1, A_CDealloc. rewrite <- (wvb_self_l md) at 1.
eapply amreal_SRr_pre; [eapply DMcdGz.seg_w1; [exact FHG | exact HF] |].
intros W' c9 _ [-> [AT MACH]].
pose proof MACH as (regs9 & mem9 & mat9 & Ec9 & _).
assert (Ec9' : c9 = cfg_at tfibsegs FGsN.A_EFA regs9 mem9 (with_vm_backing (m_vm_lazy md) mat9 md)) by (rewrite Ec9; reflexivity).
rewrite Ec9'.
eapply (FGtN.tfib_efa_spec_lk B ly X W regs9 mem9 _ c (kold + Nv) j80 j88 jst kold (rg_alloc_user (reg X c)) (rg_mapped_user (reg X c))).
- exact (EFA_PRE j80 j88 jst HJ80 HJ88 HJST HF HG _ AT MACH regs9 mem9 _ Ec9').
- intros r W3 c3 LEAF. cbn [amreal].
  eapply SRr_mono.
  + exact (DMcdGW.w2 W ly regs mem md c off kcnt kold kmf j80 j88 jst X FHG HF eq_refl HG HLr _ AT regs9 mem9 _ Ec9' r W3 c3 LEAF).
  + intros W'' c' _ HR. destruct (LEAFG j80 j88 jst HJ80 HJ88 HJST HF HG _ AT MACH regs9 mem9 _ Ec9' r W3 c3 LEAF W'' c' HR) as [HP HS].
    split; [exact HP|]. right. split; [exact HF|]. split; [exact HG|]. exact HS.
Qed.

Theorem arm_state : amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) cd_postS.
Proof.
destruct (Z.eq_dec kcnt MAXv) as [E|NE].
- destruct (Z_lt_le_dec kmf (4 * (kold + Nv))) as [G|NG].
  + exact (arm_grow E G).
  + exact (arm_nogrow (fun _ => NG)).
- exact (arm_nogrow (fun E => False_ind _ (NE E))).
Qed.
End g.

Theorem cdealloc_g_of_reads : forall (B : asyms) ARXr AOX DRq RMAXD, TfibSyms B -> rmaxd_ok RMAXD ->
  cd_reads B ARXr AOX DRq RMAXD -> cdealloc_g_t B ARXr AOX RMAXD.
Proof.
intros B ARXr AOX DRq RMAXD TB RMX RD. unfold cdealloc_g_t. intros inst ly X c off W regs mem md PRE MOD.
eapply (amreal_mono tfibsegs); [|eapply arm_state with (RMAXD := RMAXD) (inst := inst); eassumption].
intros r0 W0 c0 [HP _]. exact HP.
Qed.

Theorem cdealloc_m_of_reads : forall (B : asyms) ARXr AOX DRq RMAXD, TfibSyms B -> rmaxd_ok RMAXD ->
  cd_reads B ARXr AOX DRq RMAXD -> drq_cd DRq RMAXD -> cdealloc_m_t B ARXr AOX DRq.
Proof.
intros B ARXr AOX DRq RMAXD TB RMX RD DQ. unfold cdealloc_m_t, MnRecycle.de_cdealloc_m_t.
intros inst ly X its z zs W regs mem md PX HDR.
destruct (DQ X its z zs HDR) as [MOD RET].
assert (PRE : cd_pre_cx B ARXr inst ly X kBatchClass z W regs mem md).
{ pose proof (cr_budget_x _ _ _ _ _ RD _ _ _ _ _ _ _ _ PX _ _ HDR) as BG.
  destruct PX as (A & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
  pose proof (cr_inst _ _ _ _ _ RD _ _ _ _ _ _ A) as EI.
  unfold cd_pre_cx. repeat (split; [assumption|]). exact BG. }
eapply (amreal_mono tfibsegs); [| eapply arm_state with (RMAXD := RMAXD) (inst := inst); eassumption].
intros r W' c' [HP HS]. destruct HP as (regs' & mem' & md' & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
exists regs', mem', md'. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [|split; [exact E8 | exact E9]].
apply RET. destruct HS as [[NG Es]|(HF & HG & Es)]; rewrite Es.
- left. eapply model_step; eassumption.
- right. eapply tree_grow; eassumption.
Qed.

Theorem cdealloc_ok_of_reads : forall (B : asyms) ARXr AOX DRq NMAXD LMAXD RMAXD,
  cd_reads B ARXr AOX DRq RMAXD -> cdealloc_ok_t B ARXr AOX DRq NMAXD LMAXD RMAXD.
Proof.
intros B ARXr AOX DRq NMAXD LMAXD RMAXD RD. unfold cdealloc_ok_t. intros TB _ _ RMX _ _ _.
split; [exact (cdealloc_g_of_reads B ARXr AOX DRq RMAXD TB RMX RD) |].
intros DQ. exact (cdealloc_m_of_reads B ARXr AOX DRq RMAXD TB RMX RD DQ).
Qed.
End f.
