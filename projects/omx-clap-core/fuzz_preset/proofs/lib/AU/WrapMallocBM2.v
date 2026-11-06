(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/WrapMallocBM2.v, with its module paths and addresses changed; 31 of its 270 lines of code are new or changed and 19 lines of the source are left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025): field
   wmk_ret of the keep record wrap_malloc_walk_keep_cf (lib/Reusable/YGcfMallocComposeKeep.v:84-101) at image B, as
   WrapMallocBStmt.wmk_ret_stmt (the field verbatim; wmk_ret_of_record checks it) with segs := tfibsegs, nmax free,
   al := 8, atp := 1, acf := 1, ARX := YGcfInstBase.ARXq_cf B (fun i => i = as_inst B) (lib/Reusable/YGcfInstBase.v:480)
   at IM := AU/AGif2cgif.AImg_cgif, K := K_B (WrapMallocBM1.v). The run is WrapMallocBRetRun.retB / retN; this file
   reads no instruction.
   What carries the call segment's frames over Allocate: the post's frame (AllocG.alloc_post's view and raw clauses)
   keeps the caller's stack window outside Allocate's own window: the window is not AOXm_cf (AR_stack_law_cf for
   aowned; xs_placed_cf's disjointness from static_extents for the error buffer, at both states, layout_le keeping the
   stack bounds), not errno, and not the new block (malloc_cf_apath_success, YGcfApath.v:38, puts the block in
   blocks S2; AR_blocks_law_cf bounds it by the allocation ceiling, which layout_ok's lo_stk_ceil puts below the stack).
   ARcf at both states is read off the relation by YGcfInstBase.ARXq_cf_ARcf.
   The relation at the wrapper's return (YGcfInstBase.ARXq_cf_intro / ARX_cf_start): IOK and qtight from the relation
   at Allocate's return (ARXq_cf_iok, ARXq_cf_qtight); ARcf by AR_frame_law_ok_cf (YG0qcf.v:802), the return path
   writing only the caller's stack window below Allocate's entry sp and, on the NULL arm, errno, an image byte outside
   as_owned_static (AR_owned_image_law with TfibSyms' Tfib_owned_static, YFk0.v:772-780's argument); xs_mapped_cf from
   that ARcf (YGcfXs.ARcf_xsm, YGcfXs.v:201).
   The memnorm keep: on the block arm the run writes the stack window only (the raw memory is pointwise kept);
   on the NULL arm the writes are the stack window (above the image, off every loaded segment) and errno, whose four
   bytes are not read-only and lie below TASK_SIZE. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YB1h YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AllocG RGtop YGcfRmodel YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeKeep YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import WrapBKit WrapMallocBStmt WrapMallocBM1 WrapMallocBRetRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma vm_tr : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a (n : nat) v,
hsub H2 H1 -> (forall k, (k < n)%nat -> m2 (Z_to_bv 64 (a + Z.of_nat k)) = m1 (Z_to_bv 64 (a + Z.of_nat k))) ->
(forall k, (k < n)%nat -> off_img (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict H1 m1) a n v -> val_mem tfibsegs (mrestrict H2 m2) a n v.
Proof.
intros H1 H2 m1 m2 a n v HS Hm Ho Hv k Hk. specialize (Hv k Hk). specialize (Ho k Hk). unfold mbyte, mrestrict in *.
rewrite (Hm k Hk).
destruct (H1 (Z_to_bv 64 (a + Z.of_nat k))) eqn:E1; cbv beta iota in Hv.
- rewrite (seg_rom_none_off _ Ho) in Hv. discriminate.
- destruct (H2 (Z_to_bv 64 (a + Z.of_nat k))) eqn:E2; [rewrite (HS _ E2) in E1; discriminate | exact Hv].
Qed.
Lemma ap_tr : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a,
hsub H2 H1 -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a) -> apresent H1 m1 a -> apresent H2 m2 a.
Proof.
intros H1 H2 m1 m2 a HS Hm [Hh [b Hb]]. split.
- destruct (H2 (Z_to_bv 64 a)) eqn:E; [rewrite (HS _ E) in Hh; discriminate | reflexivity].
- exists b. rewrite Hm. exact Hb.
Qed.
Lemma vm_aview : forall (H : word -> bool) m a (w : nat) v k, val_mem tfibsegs (mrestrict H m) a w v -> (k < w)%nat ->
aview tfibsegs H m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
intros H m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma aview_mod : forall (H : word -> bool) m a, aview tfibsegs H m a = aview tfibsegs H m (bv_unsigned (Z_to_bv 64 a)).
Proof. intros H m a. unfold aview, mbyte. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Section k.
Variable B : asyms.
Hypothesis TB : TfibSyms B.

(* The caller's stack window is outside Allocate's owned set (aowned or the error buffer). *)
Lemma stack_not_AOX : forall Hp ly S (W : world tfibsegs) mem md a, ARcf tfibsegs B ly S Hp W mem md ->
ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOXm_cf B ly S a.
Proof.
intros Hp ly S W mem md a HAR Ha.
pose proof (xs_placed_of_ARcf _ _ _ _ _ _ _ _ HAR) as XSP.
intros [Ow | Xs].
- destruct (AR_laws_ok_cf tfibsegs B) as [Lb Lsh Lz Lfr Lfrs Lfl Lc Lst Lw Lly Lol Loi Lsep Lci Lhf].
exact (Lst ly S Hp W mem md a HAR Ha Ow).
- apply Exists_exists in Xs as (e & He & Hin). unfold xs_placed_cf in XSP. rewrite Forall_forall in XSP.
destruct (XSP e He) as (_ & _ & _ & D). rewrite Forall_forall in D.
assert (Hs : In (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (sec_extents ly S ++ static_extents ly ++ ly_extra ly)).
{ apply in_or_app. right. apply in_or_app. left. unfold static_extents. apply in_or_app. right. left. reflexivity. }
specialize (D _ Hs). unfold zdisjoint, in_zr in *. cbn [fst snd] in *. lia.
Qed.

Lemma errno_not_owned_cf : forall ly S Hp (W : world tfibsegs) mem md a, ARcf tfibsegs B ly S Hp W mem md ->
TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Ha O.
destruct (AR_laws_ok_cf tfibsegs B) as [Lb Lsh Lz Lfr Lfrs Lfl Lc Lst Lw Lly Lol Loi Lsep Lci Lhf].
assert (IMGa : in_img tfibsegs a).
{ unfold in_img. change tfibsegs with YB1h.TSEGS. unfold YB1h.TSEGS. eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. zlia. }
apply (proj1 (Loi ly S Hp W mem md a HAR IMGa)) in O.
rewrite (ts_owned B TB) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]). cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; zlia|] | False => destruct Hr end.
Qed.

Theorem wm_ret_B : forall nmax, wmk_ret_stmt tfibsegs B nmax 8 1 1 (YGcfInstBase.ARXq_cf B (fun i => i = as_inst B)) K_B.
Proof.
intros nmax ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2 MEN KK APRE APOST Ha0 QT PATH OOM.
pose proof MEN as (PRE & Hn & Hnmax & Hlive & Htr).
pose proof PRE as (HAR & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & _).
destruct KK as (-> & R2A & R1A & R8A & R3A & R4A & RSA & VA0 & VA1 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & PRESA).
unfold malloc_apre_cf, AllocG.alloc_pre in APRE. destruct APRE as (ARXA & RP & _).
pose proof (YGcfInstBase.ARXq_cf_ARcf B (fun i => i = as_inst B) Hp inst ly S W memA mdA ARXA) as HARA.
unfold malloc_apost_cf, AllocG.alloc_post in APOST. destruct APOST as (ARX2 & LLE & WLE & ARP & SIO & VFR & RFR & PRA).
unfold spZ, raZ, s0Z in *.
set (sp0 := bv_unsigned (getr regs 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof (cf_layout B ly S Hp _ _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof LLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LLlo & LLhi & _).
assert (SA : bv_unsigned (getr regsA 2) = sp0 - 2144) by (rewrite R2A; unfold w64; apply unsigned_lit_small; clear - Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
assert (ERRNO : as_errno B = TFIB_ERRNO) by exact (ts_errno B TB).
destruct (AR_laws_ok_cf tfibsegs B) as [Lb Lsh Lz Lfr Lfrs Lfl Lc Lst Lw Lly Lol Loi Lsep Lci Lhf].
pose proof (YGcfInstBase.ARXq_cf_ARcf B (fun i => i = as_inst B) Hp inst ly2 S2 W2 mem2 md2 ARX2) as HAR2.
(* the new block lies above the low memory and below the stack *)
assert (BLK : q <> PNull -> 4096 <= sptr_addr B ly2 q /\ sptr_addr B ly2 q + req_size n <= ly_stk_lo ly).
{ intros Hq. destruct PATH as (trc & Hp' & _).
destruct RP as (HU & HW & (SL0 & ER0 & BR0) & _).
unfold mtr_cf in Htr.
destruct (malloc_cf_apath_success (as_universe B) S n _ trc q S2 HU HW ltac:(lia) Hlive Htr SL0 ER0 BR0 Hp' Hq) as (_ & _ & _ & _ & BS2 & _ & _).
assert (Hin : In (sptr_addr B ly2 q, n) (ablocks B ly2 S2)).
{ unfold ablocks. apply (in_map (fun b => (sptr_addr B ly2 (fst b), snd b)) _ (q, n)). rewrite BS2. apply in_or_app. right. left. reflexivity. }
destruct (Lb ly2 S2 Hp W2 mem2 md2 _ _ HAR2 Hin) as (_ & L4096 & CE & _).
pose proof (lo_stk_ceil ly LO) as SC. pose proof (@YG0f.ASAN_CEIL_range rc) as [CR _].
unfold YG0f.ASAN_CEIL in *. split; [exact L4096 | lia]. }
assert (NOE : forall a, ly_stk_lo ly <= a -> ~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)).
{ intros a Ha (Hq & E1 & E2). destruct (BLK Hq) as [_ X]. lia. }
(* the raw frame over Allocate, on the caller's stack window outside Allocate's window *)
assert (FR2 : forall a, sp0 - ASTACK <= a < sp0 -> ~ (sp0 - 2144 - 4096 <= a < sp0 - 2144) -> mem2 (Z_to_bv 64 a) = memA (Z_to_bv 64 a)).
{ intros a Ha Hn2. assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
apply RFR; rewrite unsigned_lit_small by exact Ha'.
- apply (stack_not_AOX Hp ly S W memA mdA a HARA). clear - Ha Hlo Hhi; unfold ASTACK in *; lia.
- apply (stack_not_AOX Hp ly2 S2 W2 mem2 md2 a HAR2). rewrite LLlo, LLhi. clear - Ha Hlo Hhi; unfold ASTACK in *; lia.
- unfold ascratch, spZ. rewrite SA, ERRNO. unfold AllocG.AFSTACK_G. intros [X|X]; [lia | clear - X Ha Hlo T7; unfold TFIB_ERRNO, ASTACK, kHighMemBeg in *; lia].
- apply NOE. clear - Ha Hlo; unfold ASTACK in *; lia. }
assert (OFF : forall a, sp0 - ASTACK <= a < sp0 -> off_img a).
{ intros a Ha. apply off_img_high. clear - Ha Usp Hlo T7. unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *. lia. }
Ltac slot FR2 OFF WLE V := eapply (vm_tr _ _ _ _ _ _ _ WLE); [intros k Hk; apply FR2; unfold ASTACK; lia | intros k Hk; apply OFF; unfold ASTACK; lia | exact V].
assert (S0 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 2144) 8 sp0) by (slot FR2 OFF WLE VA0).
assert (S1 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 2136) 8 0x53b30) by (slot FR2 OFF WLE VA1).
assert (S2' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 8) 8 (bv_unsigned (getr regs 1))) by (slot FR2 OFF WLE V1).
assert (S8 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 16) 8 (bv_unsigned (getr regs 8))) by (slot FR2 OFF WLE V8).
assert (S9 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 24) 8 (bv_unsigned (getr regs 9))) by (slot FR2 OFF WLE V9).
assert (S18 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 32) 8 (bv_unsigned (getr regs 18))) by (slot FR2 OFF WLE V18).
assert (S19 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 40) 8 (bv_unsigned (getr regs 19))) by (slot FR2 OFF WLE V19).
assert (S20 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 48) 8 (bv_unsigned (getr regs 20))) by (slot FR2 OFF WLE V20).
assert (S21 : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sp0 - 56) 8 (bv_unsigned (getr regs 21))) by (slot FR2 OFF WLE V21).
assert (PR2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2144 - 4096)) as [A|A]; [|destruct (Z_lt_le_dec a (sp0 - 2144)) as [A'|A']].
- apply (ap_tr _ _ _ _ _ WLE (FR2 a Ha ltac:(lia)) (PRESA a Ha)).
- apply PRA. rewrite SA. unfold AllocG.AFSTACK_G. lia.
- apply (ap_tr _ _ _ _ _ WLE (FR2 a Ha ltac:(lia)) (PRESA a Ha)). }
assert (HSP : kHighMemBeg + ASTACK <= sp0 <= kHighMemEnd /\ sp0 mod 16 = 0) by (split; [lia | exact Hal]).
assert (HSP2 : getr regs2 2 = w64 (sp0 - 2144)).
{ pose proof (ARP 2 ltac:(unfold acallee_saved; lia)) as X. replace (Z_to_bv 5 2) with (2%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact R2A. }
assert (HTP2 : getr regs2 4 = w64 TFIB_TP).
{ pose proof (ARP 4 ltac:(unfold acallee_saved; lia)) as X. replace (Z_to_bv 5 4) with (4%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X, R4A, Htp, (ts_tp B TB). reflexivity. }
assert (CS2 : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsA (Z_to_bv 5 r)) by exact ARP.
unfold cfg_at. rewrite R1A. unfold w64 at 1. rewrite <- (wvb_self_m md2) at 1.
(* the registers at the caller's return, common to both arms *)
assert (REGS : forall regs', RPOST regs2 regs regs' -> getr regs' 4 = getr regs 4 -> aregs_preserved regs regs').
{ intros regs' (P2 & P8 & P9 & P18 & P19 & P20 & P21 & P3 & P4 & P22) _ r Hr. unfold acallee_saved in Hr.
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
- exact P2.
- rewrite P3. pose proof (CS2 3 ltac:(unfold acallee_saved; lia)) as X. replace (Z_to_bv 5 3) with (3%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact R3A.
- rewrite P4, Htp, (ts_tp B TB). reflexivity.
- exact P8. - exact P9. - exact P18. - exact P19. - exact P20. - exact P21.
- rewrite (P22 r Hr), (CS2 r ltac:(unfold acallee_saved; lia)). exact (RSA r Hr). }
assert (QD : {q = PNull} + {q <> PNull}) by (destruct q; first [left; reflexivity | right; discriminate]).
destruct QD as [Hq | Hq].
- (* NULL *)
subst q. assert (HA0 : getr regs2 10 = w64 0) by (rewrite Ha0; reflexivity).
eapply SRr_mono; [exact (retN W2 regs2 regs mem2 md2 (m_vm_materialized md2) HSP HSP2 HTP2 S0 S1 S2' S8 S9 S18 S19 S20 S21 Hra HA0
  (fun a Ha => PR2 a ltac:(unfold ASTACK; lia))) |].
intros W' c' _ (-> & regs' & mem' & mat & -> & RP' & R10' & FRN & ERR & PRN).
exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
assert (NST : forall a, sp0 - 2160 <= a < sp0 - 2144 -> ~ aowned B ly2 S2 a).
{ intros a Ha O. apply (Lst ly2 S2 Hp W2 mem2 md2 a HAR2); [rewrite LLlo, LLhi; clear - Ha Hlo Hhi; unfold ASTACK in *; lia | exact O]. }
assert (FRNa : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2160 <= a < sp0 - 2144) -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) ->
  aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha X1 X2. apply aview_same. apply FRN; rewrite unsigned_lit_small by exact Ha; assumption. }
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split. { apply REGS; [exact RP'|]. destruct RP' as (_ & _ & _ & _ & _ & _ & _ & _ & P4 & _). rewrite P4, Htp, (ts_tp B TB). reflexivity. }
split. { rewrite R10'. reflexivity. }
split.
{ apply YGcfInstBase.ARXq_cf_intro; [|exact (YGcfInstBase.ARXq_cf_qtight B (fun i => i = as_inst B) Hp inst ly2 S2 W2 mem2 md2 ARX2)].
assert (HARN : ARcf tfibsegs B ly2 S2 Hp W2 mem' (with_vm_backing (m_vm_lazy md2) mat md2)).
{ apply (Lfr ly2 S2 Hp W2 mem2 md2 mem' (with_vm_backing (m_vm_lazy md2) mat md2) HAR2).
- intros a Ha Ow. apply FRNa; [exact Ha | intros X; exact (NST a X Ow) | intros X; exact (errno_not_owned_cf ly2 S2 Hp W2 mem2 md2 a HAR2 X Ow)].
- intros a Hv. rewrite aview_mod in Hv |- *. pose proof (u64_range (Z_to_bv 64 a)) as Ra. set (a' := bv_unsigned (Z_to_bv 64 a)) in *. clearbody a'.
destruct (Z_lt_le_dec a' (sp0 - 2160)) as [A|A]; [|destruct (Z_lt_le_dec a' (sp0 - 2144)) as [A'|A']].
+ destruct (Z_lt_le_dec a' TFIB_ERRNO) as [B1|B1]; [|destruct (Z_lt_le_dec a' (TFIB_ERRNO + 4)) as [B2|B2]].
* rewrite FRNa; [exact Hv | exact Ra | lia | lia].
* replace a' with (TFIB_ERRNO + Z.of_nat (Z.to_nat (a' - TFIB_ERRNO))) by lia. rewrite (vm_aview _ _ _ _ _ _ ERR) by lia. discriminate.
* rewrite FRNa; [exact Hv | exact Ra | lia | lia].
+ apply apresent_aview_m. apply PRN. lia.
+ rewrite FRNa; [exact Hv | exact Ra | lia | clear - A' Hlo T7; unfold TFIB_ERRNO, ASTACK, kHighMemBeg in *; lia].
- reflexivity.
- reflexivity.
- reflexivity.
- intros a Hb Hh. apply FRN; unfold w64; rewrite unsigned_lit_small by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb; lia);
clear - Hb Hlo T7; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, TFIB_ERRNO, ASTACK in *; lia. }
exact (YGcfInstBase.ARX_cf_start B (fun i => i = as_inst B) Hp inst ly2 S2 W2 mem' (with_vm_backing (m_vm_lazy md2) mat md2)
  (YGcfInstBase.ARXq_cf_iok B (fun i => i = as_inst B) Hp inst ly2 S2 W2 mem2 md2 ARX2) HARN
  (ARcf_xsm tfibsegs B ly2 S2 Hp W2 mem' (with_vm_backing (m_vm_lazy md2) mat md2) HARN)). }
split. { apply same_io_wvb_m. }
split.
{ unfold RGtop.rkeep. split.
- intros a Ha NS. apply FRNa; [exact Ha | intros X; apply NS; left; unfold spZ; fold sp0; unfold ASTACK; lia | intros X; apply NS; right; rewrite ERRNO; exact X].
- intros x NS. apply FRN; intros X; apply NS; [left; unfold spZ; fold sp0; unfold ASTACK; lia | right; rewrite ERRNO; exact X]. }
split.
{ unfold RGtop.rwin, spZ. fold sp0. intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2160)) as [A|A]; [|destruct (Z_lt_le_dec a (sp0 - 2144)) as [A'|A']].
- apply (ap_tr (w_H W2) (w_H W2) mem2 mem' a (hsub_refl _)); [|exact (PR2 a Ha)]. apply FRN; rewrite unsigned_lit_small by (clear - Ha Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia);
[lia | clear - Ha Hlo T7; unfold TFIB_ERRNO, ASTACK, kHighMemBeg in *; lia].
- apply PRN. lia.
- apply (ap_tr (w_H W2) (w_H W2) mem2 mem' a (hsub_refl _)); [|exact (PR2 a Ha)]. apply FRN; rewrite unsigned_lit_small by (clear - Ha Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia);
[lia | clear - Ha Hlo T7; unfold TFIB_ERRNO, ASTACK, kHighMemBeg in *; lia]. }
split.
{ intros (Mi & Mt). pose proof (u64_range) as UR. split; intros x b E.
- destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 2160)) as [A|A]; [|destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 2144)) as [A'|A']].
+ destruct (Z_lt_le_dec (bv_unsigned x) TFIB_ERRNO) as [B1|B1]; [|destruct (Z_lt_le_dec (bv_unsigned x) (TFIB_ERRNO + 4)) as [B2|B2]].
* rewrite FRN in E by lia. exact (Mi x b E).
* assert (Ex : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (Hk : bv_unsigned x = TFIB_ERRNO \/ bv_unsigned x = TFIB_ERRNO + 1 \/ bv_unsigned x = TFIB_ERRNO + 2 \/ bv_unsigned x = TFIB_ERRNO + 3) by lia.
rewrite Ex. unfold TFIB_ERRNO in Hk. destruct Hk as [K|[K|[K|K]]]; rewrite K; vm_compute; reflexivity.
* rewrite FRN in E by lia. exact (Mi x b E).
+ unfold YAkMemnorm.ro_addr. rewrite tfib_find_segment_none_high; [reflexivity|]. clear - A Hlo T7. unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *. lia.
+ rewrite FRN in E by (first [lia | clear - A' Hlo T7; unfold TFIB_ERRNO, ASTACK, kHighMemBeg in *; lia]). exact (Mi x b E).
- destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 2160)) as [A|A]; [|destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 2144)) as [A'|A']].
+ destruct (Z_lt_le_dec (bv_unsigned x) TFIB_ERRNO) as [B1|B1]; [|destruct (Z_lt_le_dec (bv_unsigned x) (TFIB_ERRNO + 4)) as [B2|B2]].
* rewrite FRN in E by lia. exact (Mt x b E).
* right. unfold TASK_SIZE, TFIB_ERRNO in *. lia.
* rewrite FRN in E by lia. exact (Mt x b E).
+ right. clear - A' Hhi T4. unfold TASK_SIZE, kHighMemEnd in *. lia.
+ rewrite FRN in E by (first [lia | clear - A' Hlo T7; unfold TFIB_ERRNO, ASTACK, kHighMemBeg in *; lia]). exact (Mt x b E). }
split. { intros C. exfalso. apply C. reflexivity. }
intros _. split.
{ rewrite ERRNO. intros k Hk. exact (vm_aview _ _ _ _ _ k ERR Hk). }
specialize (OOM eq_refl). rewrite (ts_oom B TB) in OOM |- *.
rewrite FRNa; [|unfold TFIB_OOM; lia | clear - Hlo T7; unfold TFIB_OOM, ASTACK, kHighMemBeg in *; lia | unfold TFIB_OOM, TFIB_ERRNO; lia].
pose proof (vm_aview _ _ _ _ _ 0 OOM ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. rewrite X. reflexivity.
- (* a block *)
assert (HNZ : bv_unsigned (getr regs2 10) <> 0).
{ destruct (BLK Hq) as [L1 L2]. rewrite Ha0. unfold w64. rewrite unsigned_lit_small; [lia|].
pose proof (proj1 (proj2 (req_size_bounds n ltac:(lia)))) as RN. clear - L1 L2 RN Hlo Hhi T4. unfold kHighMemEnd, ASTACK in *. lia. }
eapply SRr_mono; [exact (retB W2 regs2 regs mem2 md2 (m_vm_materialized md2) HSP HSP2 HTP2 S0 S1 S2' S8 S9 S18 S19 S20 S21 Hra HNZ) |].
intros W' c' _ (-> & regs' & mem' & mat & -> & RP' & R10' & FRB).
exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
split. { unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split. { apply REGS; [exact RP'|]. destruct RP' as (_ & _ & _ & _ & _ & _ & _ & _ & P4 & _). rewrite P4, Htp, (ts_tp B TB). reflexivity. }
split. { rewrite R10'. exact Ha0. }
split.
{ apply YGcfInstBase.ARXq_cf_intro; [|exact (YGcfInstBase.ARXq_cf_qtight B (fun i => i = as_inst B) Hp inst ly2 S2 W2 mem2 md2 ARX2)].
assert (HARN : ARcf tfibsegs B ly2 S2 Hp W2 mem' (with_vm_backing (m_vm_lazy md2) mat md2)).
{ apply (Lfr ly2 S2 Hp W2 mem2 md2 mem' (with_vm_backing (m_vm_lazy md2) mat md2) HAR2).
- intros a Ha Ow. apply aview_same. apply FRB.
- intros a Hv. unfold aview, mbyte, mrestrict in Hv |- *. rewrite FRB. exact Hv.
- reflexivity.
- reflexivity.
- reflexivity.
- intros a Hb Hh. apply FRB. }
exact (YGcfInstBase.ARX_cf_start B (fun i => i = as_inst B) Hp inst ly2 S2 W2 mem' (with_vm_backing (m_vm_lazy md2) mat md2)
  (YGcfInstBase.ARXq_cf_iok B (fun i => i = as_inst B) Hp inst ly2 S2 W2 mem2 md2 ARX2) HARN
  (ARcf_xsm tfibsegs B ly2 S2 Hp W2 mem' (with_vm_backing (m_vm_lazy md2) mat md2) HARN)). }
split. { apply same_io_wvb_m. }
split. { unfold RGtop.rkeep. split; [intros a Ha NS; apply aview_same; apply FRB | intros x NS; apply FRB]. }
split. { unfold RGtop.rwin, spZ. fold sp0. intros a Ha. apply (ap_tr (w_H W2) (w_H W2) mem2 mem' a (hsub_refl _) (FRB _) (PR2 a Ha)). }
split. { intros (Mi & Mt). split; intros x b E; rewrite FRB in E; [exact (Mi x b E) | exact (Mt x b E)]. }
split. { intros _ i Hi. apply FRB. }
intros E. exfalso. exact (Hq E).
Qed.
End k.
End c.
