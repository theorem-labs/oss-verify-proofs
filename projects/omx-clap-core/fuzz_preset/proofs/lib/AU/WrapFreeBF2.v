(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025): field
   wfrk_ret of the primed keep record wrap_free_walk_keep_cf_rh (lib/Reusable/YGcfMallocComposeKeep.v:408-422)
   at image B, as WrapFreeBStmt.wf_ret_stmt (the field verbatim; wf_ret_of_record checks it) with segs := tfibsegs,
   atpD := 1 (FROM_MALLOC, asan_free's a5), ARX := YGcfInstBase.ARXq_cf (YGcfInstBase.v:480) at IM := AGif2cgif.AImg_cgif
   and IOK := (fun i => i = as_inst B), K := K_F.
   K_F, the invariant from the call segment (WrapFreeBF1.v) to this one, carries what the interceptor's epilogue reads
   after Deallocate returns: the stack pointer and return address at Deallocate's entry (asan_free tail-jumps, so
   Deallocate returns to ___interceptor_free + 0x1a8), the callee-saved registers the call segment keeps, the seven
   saved registers in the interceptor's frame, and the caller's stack window present.
   The run is WrapFreeBRet.seg_ret (the ten-instruction epilogue, ported from YFh1.v:336-370); this file reads no
   instruction. What carries the frame over Deallocate: the primed post YGcfRehidePost.dealloc_post_raw_rh
   (YGcfRehidePost.v:395-401). Its raw frame keeps the caller's stack window outside Deallocate's own window: the window
   is not aowned (AR_stack_law_cf at both states, layout_le keeping the stack bounds), not errno, and not the freed block
   (YGcfBlockRange.block_user_range_cf, YGcfBlockRange.v:31, puts a live block below the stack). Its hidden-set bound
   wle_in grows the hidden set only inside dead_shadow_new, which lies below kHighMemBeg
   (YGcfRehidePost.dead_shadow_new_high, YGcfRehidePost.v:244), so the window stays visible.
   The post's ARX is built by ARXq_cf_intro / ARX_cf_start: IOK from the post's ARX (ARXq_cf_iok), ARcf by
   AR_laws_ok_cf's frame law (the epilogue stores nothing; the model changes by materialization only), xs_mapped_cf by
   YGcfXs.ARcf_xsm (YGcfXs.v:201), qtight the field's premise. The memnorm keep holds as the memory is unchanged.
   Port: the block arm of the malloc walk's lib/AU/WrapMallocBM2.v (its return-segment proof), whose
   helpers ap_tr (WrapMallocBM2.v:63-69) and wvb_self_m / same_io_wvb_m (WrapMallocBM1.v:55-58) are restated here
   with the suffix _f (the free walk does not import the malloc walk's field files). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DeallocG RGtop YGcfRmodel YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfBlockRange YGcfXs YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif WrapBKit WrapFreeBStmt WrapFreeBRet.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* wvb_self_m / same_io_wvb_m (lib/AU/WrapMallocBM1.v) *)
Lemma wvb_self_f : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_wvb_f : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. unfold same_io. destruct md; cbn; repeat split; reflexivity. Qed.
(* ap_tr (lib/AU/WrapMallocBM2.v) *)
Lemma ap_tr_f : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a,
hsub H2 H1 -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a) -> apresent H1 m1 a -> apresent H2 m2 a.
Proof.
intros H1 H2 m1 m2 a HS Hm [Hh [b Hb]]. split.
- destruct (H2 (Z_to_bv 64 a)) eqn:E; [rewrite (HS _ E) in Hh; discriminate | reflexivity].
- exists b. rewrite Hm. exact Hb.
Qed.

Section k.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
(* The record's call-site relation at image B. *)
Local Notation ARXB := (YGcfInstBase.ARXq_cf (IM := AImg_cgif) B (fun i => i = as_inst B)).

(* The invariant from the call segment to the return segment (see the header). *)
Definition K_F : Kfree_t tfibsegs := fun ly S Hp W regs mem md p n ch W1 regsD memD mdD =>
W1 = W /\ getr regsD 2 = w64 (spZ regs - 2128) /\ getr regsD 1 = w64 RA_FREE /\
getr regsD 8 = getr regs 2 /\ getr regsD 3 = getr regs 3 /\ getr regsD 4 = getr regs 4 /\
(forall r : Z, 22 <= r <= 27 -> getr regsD (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 8) 8 (raZ regs) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 16) 8 (s0Z regs) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem tfibsegs (mrestrict (w_H W) memD) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
(forall a, spZ regs - ASTACK <= a < spZ regs -> apresent (w_H W) memD a).

Theorem wf_ret_B : wf_ret_stmt tfibsegs B 1 ARXB K_F.
Proof.
intros ly S Hp W regs mem md p n ch W1 inst so bp regsD memD mdD ly2 S2 W2 regs2 mem2 md2 FEN KK DPRE DPOST QT PATH.
pose proof FEN as (PRE & Hpn & Ha0 & Hnh & Htr).
pose proof PRE as (HAR & Hra & Hal & Hlo & Hbot & Hhi & HPRES & _).
destruct KK as (-> & R2D & R1D & R8D & R3D & R4D & RSD & V1 & V8 & V9 & V18 & V19 & V20 & V21 & PRESD).
unfold free_dpre_cf, DeallocG.dealloc_pre in DPRE. destruct DPRE as (ARXD & RP & _).
unfold YGcfRehidePost.dealloc_post_raw_rh, YGcfRehidePost.dealloc_post_rh in DPOST.
destruct DPOST as ((ARX2 & LLE & WLE & ARP & SIO & VFR & PRA) & RFR).
unfold spZ, raZ, s0Z in *.
set (sp0 := bv_unsigned (getr regs 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof (cf_layout B ly S Hp _ _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (lo_stk_ceil ly LO) as SC.
pose proof LLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LLlo & LLhi & _).
assert (SD : bv_unsigned (getr regsD 2) = sp0 - 2128) by (rewrite R2D; unfold w64; apply unsigned_lit_small; clear - Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
assert (ERRNO : as_errno B = TFIB_ERRNO) by exact (ts_errno B TB).
destruct (AR_laws_ok_cf tfibsegs B) as [Lb Lsh Lz Lfr Lfrs Lfl Lc Lst Lw Lly Lol Loi Lsep Lci Lhf].
assert (HAR2 : ARcf tfibsegs B ly2 S2 Hp W2 mem2 md2) by exact (YGcfInstBase.ARXq_cf_ARcf B _ _ _ _ _ _ _ _ ARX2).
assert (HARD : ARcf tfibsegs B ly (finit_cf S) Hp W memD mdD) by exact (YGcfInstBase.ARXq_cf_ARcf B _ _ _ _ _ _ _ _ ARXD).
(* the freed block lies below the stack (YGcfBlockRange.block_user_range_cf) *)
assert (NOE : forall a, ly_stk_lo ly <= a -> ~ (p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)).
{ intros a Ha (Hq & E1 & E2). destruct Hpn as [Hp0 | Hin]; [exact (Hq Hp0)|].
destruct (YGcfBlockRange.block_user_range_cf tfibsegs B ly S Hp W mem md p n HAR Hin) as (_ & [[_ L2] | [_ L2]]).
- clear - E2 L2 Ha T7. unfold kLowShadowBeg, kHighMemBeg in *. lia.
- clear - E2 L2 Ha SC. first [lia | unfold YG0f.ASAN_CEIL in *; lia]. }
(* the raw frame over Deallocate, on the caller's stack window outside Deallocate's window *)
assert (FR2 : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2128 - DeallocG.DFSTACK_G <= a < sp0 - 2128) -> mem2 (Z_to_bv 64 a) = memD (Z_to_bv 64 a)).
{ intros a Ha Hn2. assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
apply RFR; rewrite unsigned_lit_small by exact Ha'.
- apply (Lst ly (finit_cf S) Hp W memD mdD a HARD). clear - Ha Hlo Hhi; unfold ASTACK in *; lia.
- apply (Lst ly2 S2 Hp W2 mem2 md2 a HAR2). rewrite LLlo, LLhi. clear - Ha Hlo Hhi; unfold ASTACK in *; lia.
- unfold ascratch, spZ. rewrite SD, ERRNO. intros [X|X]; [lia | clear - X Ha Hlo T7; unfold TFIB_ERRNO, ASTACK, kHighMemBeg in *; lia].
- apply NOE. clear - Ha Hlo; unfold ASTACK in *; lia. }
(* there the hidden set did not grow: the primed post's wle_in grows it only inside dead_shadow_new, which lies below
   kHighMemBeg (YGcfRehidePost.dead_shadow_new_high), and the window is above it *)
assert (OUT : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2128 - DeallocG.DFSTACK_G <= a < sp0 - 2128) ->
  w_H W2 (Z_to_bv 64 a) = false /\ w_H W (Z_to_bv 64 a) = false /\ mem2 (Z_to_bv 64 a) = memD (Z_to_bv 64 a)).
{ intros a Ha Hd. destruct (PRESD a Ha) as [Hh _]. split; [|split; [exact Hh | exact (FR2 a Ha Hd)]].
destruct (w_H W2 (Z_to_bv 64 a)) eqn:EH; [|reflexivity].
destruct (WLE _ EH) as [EW|ED]; [rewrite EW in Hh; discriminate|]. exfalso.
rewrite unsigned_lit_small in ED by (clear - Ha Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
apply (YGcfRehidePost.dead_shadow_new_high ly (finit_cf S) S2 a); [|exact ED].
clear - Ha Hlo T7. unfold ASTACK in *. lia. }
assert (HSP2 : getr regs2 2 = w64 (sp0 - 2128)).
{ pose proof (ARP 2 ltac:(unfold acallee_saved; lia)) as X. replace (Z_to_bv 5 2) with (2%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact R2D. }
assert (SD2 : bv_unsigned (getr regs2 2) = sp0 - 2128) by (rewrite HSP2; unfold w64; apply unsigned_lit_small; clear - Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
(* the seven saved words, read at Deallocate's return *)
assert (TV : forall a v, sp0 - 56 <= a -> a + 8 <= sp0 ->
  val_mem tfibsegs (mrestrict (w_H W) memD) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v A1 A2 Hv k Hk. rewrite <- (Hv k Hk).
assert (Hx : sp0 - ASTACK <= a + Z.of_nat k < sp0) by (clear - A1 A2 Hk; unfold ASTACK; lia).
destruct (OUT (a + Z.of_nat k) Hx ltac:(clear - A1 A2 Hk; lia)) as (H2 & H1 & M2).
unfold mbyte, mrestrict. rewrite H1, H2, M2. reflexivity. }
assert (S1 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (bv_unsigned (getr regs2 2) + 2120) 8 (bv_unsigned (getr regs 1))).
{ rewrite SD2. replace (sp0 - 2128 + 2120) with (sp0 - 8) by lia. apply TV; [lia | lia | exact V1]. }
assert (S8 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (bv_unsigned (getr regs2 2) + 2112) 8 (bv_unsigned (getr regs 8))).
{ rewrite SD2. replace (sp0 - 2128 + 2112) with (sp0 - 16) by lia. apply TV; [lia | lia | exact V8]. }
assert (S9 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (bv_unsigned (getr regs2 2) + 2104) 8 (bv_unsigned (getr regs 9))).
{ rewrite SD2. replace (sp0 - 2128 + 2104) with (sp0 - 24) by lia. apply TV; [lia | lia | exact V9]. }
assert (S18 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (bv_unsigned (getr regs2 2) + 2096) 8 (bv_unsigned (getr regs 18))).
{ rewrite SD2. replace (sp0 - 2128 + 2096) with (sp0 - 32) by lia. apply TV; [lia | lia | exact V18]. }
assert (S19 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (bv_unsigned (getr regs2 2) + 2088) 8 (bv_unsigned (getr regs 19))).
{ rewrite SD2. replace (sp0 - 2128 + 2088) with (sp0 - 40) by lia. apply TV; [lia | lia | exact V19]. }
assert (S20 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (bv_unsigned (getr regs2 2) + 2080) 8 (bv_unsigned (getr regs 20))).
{ rewrite SD2. replace (sp0 - 2128 + 2080) with (sp0 - 48) by lia. apply TV; [lia | lia | exact V20]. }
assert (S21 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (bv_unsigned (getr regs2 2) + 2072) 8 (bv_unsigned (getr regs 21))).
{ rewrite SD2. replace (sp0 - 2128 + 2072) with (sp0 - 56) by lia. apply TV; [lia | lia | exact V21]. }
(* the caller's stack window is present after Deallocate *)
assert (PR2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2128 - DeallocG.DFSTACK_G)) as [A|A]; [|destruct (Z_lt_le_dec a (sp0 - 2128)) as [A'|A']].
- destruct (OUT a Ha ltac:(lia)) as (H2 & _ & M2). destruct (PRESD a Ha) as [_ [b Hb]].
split; [exact H2|]. exists b. rewrite M2. exact Hb.
- apply PRA. unfold spZ. rewrite SD. lia.
- destruct (OUT a Ha ltac:(lia)) as (H2 & _ & M2). destruct (PRESD a Ha) as [_ [b Hb]].
split; [exact H2|]. exists b. rewrite M2. exact Hb. }
assert (Hlo2 : kHighMemBeg <= bv_unsigned (getr regs2 2)) by (rewrite SD2; clear - Hlo T7; unfold ASTACK in *; lia).
assert (Hhi2 : bv_unsigned (getr regs2 2) + 2128 <= kHighMemEnd) by (rewrite SD2; clear - Hhi T4; lia).
assert (Hal2 : bv_unsigned (getr regs2 2) mod 16 = 0).
{ rewrite SD2. replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
assert (CS2 : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsD (Z_to_bv 5 r)) by exact ARP.
unfold cfg_at.
replace (w64 (bv_unsigned (getr regsD 1))) with (w64 RA_FREE) by (rewrite R1D; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
rewrite <- (wvb_self_f md2) at 1.
eapply SRr_mono; [exact (seg_ret W2 regs regs2 mem2 md2 (m_vm_materialized md2) Hlo2 Hhi2 Hal2 Hra S1 S8 S9 S18 S19 S20 S21) |].
intros W' c' _ (-> & regs' & mem' & mat & -> & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & P3 & P4 & P22 & FRB).
exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ (22 <= r <= 27)) by lia. clear Hr.
destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|Hr]]]]]]]]].
all: try (lazymatch goal with |- context [Z_to_bv 5 ?k] => let kb := eval vm_compute in (Z.to_nat k) in
  lazymatch kb with
  | 2%nat => replace (Z_to_bv 5 k) with (2%bv : bv 5) by (apply bv_eq; reflexivity)
  | 3%nat => replace (Z_to_bv 5 k) with (3%bv : bv 5) by (apply bv_eq; reflexivity)
  | 4%nat => replace (Z_to_bv 5 k) with (4%bv : bv 5) by (apply bv_eq; reflexivity)
  | 8%nat => replace (Z_to_bv 5 k) with (8%bv : bv 5) by (apply bv_eq; reflexivity)
  | 9%nat => replace (Z_to_bv 5 k) with (9%bv : bv 5) by (apply bv_eq; reflexivity)
  | 18%nat => replace (Z_to_bv 5 k) with (18%bv : bv 5) by (apply bv_eq; reflexivity)
  | 19%nat => replace (Z_to_bv 5 k) with (19%bv : bv 5) by (apply bv_eq; reflexivity)
  | 20%nat => replace (Z_to_bv 5 k) with (20%bv : bv 5) by (apply bv_eq; reflexivity)
  | 21%nat => replace (Z_to_bv 5 k) with (21%bv : bv 5) by (apply bv_eq; reflexivity)
  end end).
- rewrite P2, SD2. unfold w64, sp0. replace (bv_unsigned (getr regs 2) - 2128 + 2128) with (bv_unsigned (getr regs 2)) by lia. apply Z_to_bv_bv_unsigned.
- rewrite P3. pose proof (CS2 3 ltac:(unfold acallee_saved; lia)) as X. replace (Z_to_bv 5 3) with (3%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact R3D.
- rewrite P4. pose proof (CS2 4 ltac:(unfold acallee_saved; lia)) as X. replace (Z_to_bv 5 4) with (4%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact R4D.
- exact P8. - exact P9. - exact P18. - exact P19. - exact P20. - exact P21.
- rewrite (P22 r Hr), (CS2 r ltac:(unfold acallee_saved; lia)). exact (RSD r Hr). }
split.
{ assert (HARP : ARcf tfibsegs B ly2 S2 Hp W2 mem' (with_vm_backing (m_vm_lazy md2) mat md2)).
{ apply (Lfr ly2 S2 Hp W2 mem2 md2 mem' (with_vm_backing (m_vm_lazy md2) mat md2) HAR2).
- intros a Ha Ow. apply aview_same. apply FRB.
- intros a Hv. unfold aview, mbyte, mrestrict in Hv |- *. rewrite FRB. exact Hv.
- reflexivity.
- reflexivity.
- reflexivity.
- intros a Hb Hh. apply FRB. }
apply YGcfInstBase.ARXq_cf_intro; [|exact QT].
apply YGcfInstBase.ARX_cf_start.
- exact (YGcfInstBase.ARXq_cf_iok B _ _ _ _ _ _ _ _ ARX2).
- exact HARP.
- exact (YGcfXs.ARcf_xsm _ _ _ _ _ _ _ _ HARP). }
split. { apply same_io_wvb_f. }
split. { unfold RGtop.rkeep. split; [intros a Ha NS; apply aview_same; apply FRB | intros x NS; apply FRB]. }
split. { unfold RGtop.rwin, spZ. fold sp0. intros a Ha. apply (ap_tr_f (w_H W2) (w_H W2) mem2 mem' a (hsub_refl _) (FRB _) (PR2 a Ha)). }
split. { intros (Mi & Mt). split; intros x b E; rewrite FRB in E; [exact (Mi x b E) | exact (Mt x b E)]. }
intros i Hi. apply FRB.
Qed.
End k.
End c.
