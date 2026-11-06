(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/WrapFreeBF1.v, with its module paths, module names and addresses changed; 15 of its 342 lines of code are new or changed and 14 lines of the source are left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025): field
   wfrk_call of the primed keep record wrap_free_walk_keep_cf_rh (lib/Reusable/YGcfMallocComposeKeep.v:399-407)
   at image B, as WrapFreeBStmt.wf_call_stmt (the field verbatim; wf_call_of_record checks it), with
     segs := tfibsegs, atpD := 1 (FROM_MALLOC), ARX := YGcfInstBase.ARXq_cf (YGcfInstBase.v:480) at
     IM := AGif2cgif.AImg_cgif and IOK := (fun i => i = as_inst B), K := WrapFreeBF2.K_F,
   and these premises: TfibSyms B; cf_pc_deallocate = Deallocate's entry (YB1w's symbol, 0x32390, AU/CfImgB.v's
   field). The stack room Deallocate's entry asks below the interceptor's frame of 2128 is acall_pre_cf's conjunct
   ly_bot ly + ACALL_PREFIX < spZ regs (YG0dcf.v:225, ACALL_PREFIX := 4096).
   The callees internal_allocator() and BufferedStackTrace::UnwindImpl are discharged by the image-B theorems
   YFfg.tfib_ialloc_ok and YFl4.tfib_unwind_ok (no premise left for them).
   The run is WrapFreeBCall.seg_call; this file reads no instruction.
   ARcf after the segment, at finit_cf S (= set_internal_inited true S, Deallocate's entry state): the interceptor
   wrote the caller's stack window, T + t_unwinding and the internal allocator's zone; WrapFreeBFinn.free_finn_ARcf_B
   rebuilds ARcf there. Its premises are discharged as FINH (lib/Reusable/YFg3.v) discharges YFf0.free_finn_ARm's:
   the agreement outside the writes (AG), the visibility (VIS), the unwinding byte, the internal allocator's cells
   (IAL_POST), the constant cells (CONST_OUT, YFg3.v:274-304, over YFfy.Tfib_const_loc) and the hidden shadow (HSK).
   The ARX at Deallocate's entry is built by ARXq_cf_intro / ARX_cf_start: IOK by ts_inst, ARcf as above, xs_mapped_cf
   by YGcfXs.ARcf_xsm (YGcfXs.v:201), qtight from acall_pre_cf's qmeter_cf (finit_cf moves no quarantine field).
   ikeep_mn_cf (YGcfMallocComposeKeep.v:57-62): outside aowned at S and the caller's scratch the memory is the
   caller's (T + t_unwinding and the internal allocator's zone are owned, WrapFreeBFinn.D_owned_cf); the overlay normal
   form is kept (the stack window lies above the image and below TASK_SIZE; the internal allocator's zone lies in a
   writable segment).
   Helpers vm1_raw_f, vm_aview_f: restated from WrapMallocBM1.v and WrapMallocBM2.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgCellsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YB13 YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFeq YFfy YFfg YFl4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DeallocG RGtop YGcfRmodel YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfXs YGcfInstBase YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require WrapFreeBCall WrapFreeBFinn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif WrapBKit WrapFreeBStmt WrapFreeBRet WrapFreeBF2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* vm1_raw (lib/AU/WrapMallocBM1.v) *)
Lemma vm1_raw_f : forall (H : word -> bool) m a v, val_mem tfibsegs (mrestrict H m) a 1 v -> off_img a ->
m (Z_to_bv 64 a) = Some (Z_to_bv 8 (le_byte v 1 0)).
Proof.
intros H m a v Hv Ha. pose proof (Hv 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E. unfold mbyte, mrestrict in E.
destruct (H (Z_to_bv 64 a)); [rewrite (seg_rom_none_off a Ha) in E; discriminate|].
destruct (m (Z_to_bv 64 a)); [exact E | rewrite (seg_rom_none_off a Ha) in E; discriminate].
Qed.
(* vm_aview (lib/AU/WrapMallocBM2.v) *)
Lemma vm_aview_f : forall (H : word -> bool) m a (w : nat) v k, val_mem tfibsegs (mrestrict H m) a w v -> (k < w)%nat ->
aview tfibsegs H m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
intros H m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* An address of the image's writable segments (tfib_rw_window's case split, lib/Reusable/YB13.v) is not read-only. *)
Lemma ro_img_rw_f : forall x : word, 0xa2000 <= bv_unsigned x < 0x601000 -> YAkMemnorm.ro_addr tfibsegs x = false.
Proof.
intros x Hx. unfold YAkMemnorm.ro_addr.
destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:Hf; [|reflexivity].
apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
rewrite tfib_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
AsanUbsan_segment_000 AsanUbsan_segment_001 AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
all: first [ exfalso; lia | reflexivity | vm_compute; reflexivity | exfalso; cbn in Hb, Ht; lia ].
Qed.

Section k.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Hypothesis HpcD : cf_pc_deallocate = tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE.
(* The record's call-site relation at image B. *)
Local Notation ARXB := (YGcfInstBase.ARXq_cf (IM := AImg_cgif) B (fun i => i = as_inst B)).

Section e.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world tfibsegs) (regs : bvmap 5 word).
Variables (mem : word -> option byte) (md : Model) (p : sptr) (n : Z) (ch : list (Z * Z * Z)).
Hypothesis FEN : fentry_cf tfibsegs B ly S Hp W regs mem md p n ch.
Hypothesis RP : rpreD_free_cf B (finit_cf S) n.
Let PRE : acall_pre_cf tfibsegs B ly S Hp W regs mem md ch := proj1 FEN.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation WINf := (WrapFreeBCall.WIN ly regs).

Lemma Hsp_f : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly.
Proof. pose proof PRE as (_ & _ & _ & H1 & H2 & H3 & _). unfold spZ in *. unfold sp0. lia. Qed.

(* YFgn.v:416-436 over WrapFreeBCall.WIN *)
Lemma notWIN_img_f : forall a, TFIB_IMG_LO <= a < TFIB_IMG_END -> ~ WINf a.
Proof.
intros a Ha Hw. pose proof (WrapFreeBCall.LYB B ly S Hp W regs mem md ch PRE) as (F1 & F2 & F3 & F4 & F5 & F6 & HF). pose proof Hsp_f as (S1 & S2 & S3).
unfold WrapFreeBCall.WIN in Hw. destruct Hw as [Hs | Ht].
- clear - Ha Hs S1 S2 S3 HF. ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. unfold sp0 in *. lia.
- clear - Ha Ht F1. ceil; unfold zone3, zone3cases, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. lia.
Qed.
Lemma notWIN_shb_f : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ WINf a.
Proof.
intros a Ha Hw. pose proof (WrapFreeBCall.LYB B ly S Hp W regs mem md ch PRE) as (F1 & F2 & F3 & F4 & F5 & F6 & HF). pose proof Hsp_f as (S1 & S2 & S3).
unfold WrapFreeBCall.WIN in Hw. destruct Hw as [Hs | Ht].
- clear - Ha Hs S1 S2 S3 HF. ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. unfold sp0 in *. lia.
- clear - Ha Ht F1. ceil; unfold zone3, zone3cases, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. lia.
Qed.
Lemma notWIN_Thead_f : forall a, ly_T ly <= a < ly_T ly + 80 -> ~ WINf a.
Proof.
intros a Ha Hw. pose proof (WrapFreeBCall.stack_ivs B ly S Hp W regs mem md ch PRE) as (IT & _).
unfold WrapFreeBCall.WIN in Hw. unfold kThreadObjSize, ASTACK, t_unwinding in *. lia.
Qed.
Lemma notWIN_C_f : forall a, ly_C ly <= a < ly_C ly + 256 -> ~ WINf a.
Proof.
intros a Ha Hw.
pose proof (WrapFreeBCall.stack_ivs B ly S Hp W regs mem md ch PRE) as (_ & _ & IC & _).
pose proof (WrapFreeBCall.LYD B ly S Hp W regs mem md ch PRE) as (_ & (_ & _ & DTC & _) & _).
unfold zdisjoint in DTC. cbn [fst snd] in DTC.
unfold WrapFreeBCall.WIN in Hw. unfold kThreadObjSize, ASTACK, t_unwinding in *. lia.
Qed.
(* YFgn.v:150-166 *)
Lemma LYBD_f : zone3 (ly_D ly) 4096 /\ ly_D ly + 4096 <= ASAN_CEIL /\
(ly_prim ly + kPrimResvSize <= ly_D ly \/ ly_D ly + 4096 <= ly_prim ly) /\
(ly_T ly + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= ly_T ly) /\
(ly_D ly + 4096 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_D ly).
Proof.
pose proof (WrapFreeBCall.LY B ly S Hp W regs mem md ch PRE) as LY.
pose proof (WrapFreeBCall.IMG B ly S Hp W regs mem md ch PRE) as IMG.
pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth_f _ _ 7 _ (lo_app ly LY) eq_refl) as ID. cbn beta in ID. cbn [fst snd] in ID.
pose proof (zone3_intro ly (ly_D ly) 4096 IMG ltac:(clear_all; lia) ID (pairwise_ij_f _ _ 7 1 _ _ HD eq_refl eq_refl)) as ZD.
unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & _ & DD & _).
do 6 (apply Forall_cons_iff in DP as [_ DP]). apply Forall_cons_iff in DP as [PD _].
do 4 (apply Forall_cons_iff in DT as [_ DT]). apply Forall_cons_iff in DT as [TD _].
apply Forall_cons_iff in DD as [DSTK _].
unfold zdisjoint in *. cbn [fst snd] in *.
split; [exact ZD|]. split; [clear - ZD; unfold zone3 in ZD; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia|]. repeat split; assumption.
Qed.
Lemma notWIN_D_f : forall a, ly_D ly <= a < ly_D ly + 4096 -> ~ WINf a.
Proof.
intros a Ha Hw. pose proof LYBD_f as (D1 & D2 & PD & TD & DSTK). pose proof Hsp_f as Hsp.
unfold WrapFreeBCall.WIN in Hw. clear - Ha Hw DSTK TD Hsp. unfold ASTACK, t_unwinding, kThreadObjSize in *. unfold sp0 in *. lia.
Qed.
Lemma HTSD_f : ly_tsd ly = TFIB_TSD.
Proof. rewrite (amc_tsd _ _ _ _ _ (proj1 (proj1 PRE))). exact (ts_tsd B TB). Qed.

(* YFg3.v:274-304: the constant cells lie outside the walk's writes. *)
Lemma CONST_OUT_f : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ WINf (aeval B ly (c_at c) + i) /\ ~ WrapFreeBCall.IZONE (aeval B ly (c_at c) + i) /\
0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (YFfy.Tfib_const_loc ly) c Hc) as K. unfold YFfy.const_loc_ok in K; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
assert (LOW : forall a, YFfy.low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ WINf (a + i) /\ ~ WrapFreeBCall.IZONE (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold YFfy.low_ok in L; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFIB_IMG_LO <= a /\ a + w <= TFIB_IAL_LO) \/ (TFIB_IAL_HI <= a /\ a + w <= TFIB_IAL_FLAG) \/ (TFIB_IAL_FLAG + 4 <= a /\ a + w <= TFIB_IMG_END) \/
(SHADOW_OFF + TFIB_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFIB_IMG_END / 8)) by lia.
clear L. unfold WrapFreeBCall.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
change (YImgTop.IMG_LO_B / 8) with 8192 in R. change (YImgTop.IMG_TOP_B / 8) with (YImgTop.IMG_TOP_B / 8) in R.
(* the constant quotients as numerals: lia here treats a constant [_ / 8] as an atom *)
repeat match type of R with context [?x / 8] => let v := eval vm_compute in (x / 8) in change (x / 8) with v in R end.
split; [|lia]. destruct R as [R|[R|[R|R]]].
1-3: apply notWIN_img_f; unfold TFIB_IMG_LO, TFIB_IMG_END; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *; lia.
apply notWIN_shb_f; unfold kLowShadowBeg, kHighMemBeg; lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- pose proof (WrapFreeBCall.LYB B ly S Hp W regs mem md ch PRE) as (LB & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
split; [apply notWIN_Thead_f; lia|].
unfold WrapFreeBCall.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
- pose proof (WrapFreeBCall.LYB B ly S Hp W regs mem md ch PRE) as (_ & _ & _ & _ & _ & _ & LB & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
split; [apply notWIN_C_f; lia|].
unfold WrapFreeBCall.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
- rewrite HTSD_f. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- pose proof LYBD_f as (HD1 & HD2 & _). ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HD1, HD2; unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
split; [apply notWIN_D_f; lia|].
unfold WrapFreeBCall.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.

Lemma wf_call_at : SRr tfibsegs W (cfg_at tfibsegs (pc_wrap_free (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsD memD mdD,
    c1 = cfg_at tfibsegs cf_pc_deallocate regsD memD mdD /\
    free_dpre_cf tfibsegs B 1 ARXB Hp inst so bp ly (finit_cf S) W1 regsD memD mdD p n (ftr_cf B ly regs ch) /\
    same_io md mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    YGcfMallocComposeKeep.ikeep_mn_cf tfibsegs B ly S regs W mem W1 memD /\ errno_kept_cf B mem memD /\
    K_F ly S Hp W regs mem md p n ch W1 regsD memD mdD).
Proof.
pose proof FEN as (PRE' & Hpn & Ha0 & Hnh & Htr).
pose proof PRE as (HAR & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & QM & SL & ER & AB & BR).
pose proof Hsp_f as (Hlo' & Hbot' & Hhi').
unfold spZ, raZ in Hal, Hlo, Hbot, Hhi, HPRES.
fold sp0 in Hal, Hlo, Hbot, Hhi, HPRES.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof (cf_layout B ly S Hp _ _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (lo_stk_ceil ly LO) as SC.
pose proof (WrapFreeBCall.LYB B ly S Hp W regs mem md ch PRE) as LB.
pose proof (WrapFreeBCall.stack_ivs B ly S Hp W regs mem md ch PRE) as (IT & _).
pose proof (WrapFreeBCall.IMG B ly S Hp W regs mem md ch PRE) as IMGc.
pose proof CONST_OUT_f as CO.
destruct (AR_laws_ok_cf tfibsegs B) as [Lb Lsh Lz Lfr Lfrs Lfl Lc Lst Lw Lly Lol Loi Lsep Lci Lhf].
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
(* the pointer is below 2 ^ 47 *)
assert (HP47 : bv_unsigned (getr regs 10) < 2 ^ 47).
{ rewrite Ha0. destruct Hpn as [-> | Hin].
- change (sptr_addr B ly PNull) with 0. unfold w64. rewrite unsigned_lit_small by lia. lia.
- assert (Hin' : In (sptr_addr B ly p, n) (ablocks B ly S)).
{ unfold ablocks. apply (in_map (fun b => (sptr_addr B ly (fst b), snd b)) _ (p, n)). exact Hin. }
destruct (Lb ly S Hp W mem md _ _ HAR Hin') as (_ & L4096 & CE & _ & _ & _ & Hn0).
pose proof (req_size_bounds n ltac:(lia)) as (_ & RN & _).
pose proof (@YG0f.ASAN_CEIL_range rc) as [[_ CR] _]. unfold YG0f.ASAN_CEIL in CR.
unfold w64. rewrite unsigned_lit_small by lia. lia. }
unfold ftr_cf. rewrite (ts_code B TB) in *. cbn [pc_wrap_free pc_free_ra0 Tfib_code] in *.
unfold cfg_at. rewrite <- (wvb_self_f md) at 1.
eapply SRr_mono; [exact (WrapFreeBCall.seg_call B TB ly S Hp W regs mem md ch (m_vm_materialized md) PRE HP47 tfib_ialloc_ok tfib_unwind_ok) |].
intros W' c' _ (-> & regsD & memD & mat & -> & R1 & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R8 & R3 & R4 & RS
& MEQI1 & UNW & PRES & OBJ0 & OBJ1 & TRA & V1 & V8 & V9 & V18 & V19 & V20 & V21).
fold sp0 in R2, R14, PRES, OBJ0, OBJ1, TRA, V1, V8, V9, V18, V19, V20, V21 |- *.
destruct MEQI1 as [MEQ IP]. unfold WrapFreeBCall.MEQ in MEQ.
assert (LEN : (1 <= length (call_trace ly B_INTERCEPTOR_FREE_PC_OFF_138 regs ch) <= 30)%nat).
{ unfold call_trace. destruct (frame0_ok ly regs); [apply unwind_of_chain_length | cbn; lia]. }
assert (UNW0 : val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0) by exact (cf_unwinding_val B ly S Hp (w_H W) mem (proj1 HAR)).
assert (OFFT : off_img (ly_T ly + t_unwinding)).
{ apply (zone3_off_img _ _ _ (proj1 LB)). unfold kThreadObjSize, t_unwinding. lia. }
assert (TRAW : memD (Z_to_bv 64 (ly_T ly + t_unwinding)) = mem (Z_to_bv 64 (ly_T ly + t_unwinding))).
{ rewrite (vm1_raw_f _ _ _ _ UNW OFFT), (vm1_raw_f _ _ _ _ UNW0 OFFT). reflexivity. }
(* the writes are owned at S or in the caller's stack window (WrapFreeBFinn.D_owned_cf) *)
assert (OWN : forall a, 0 <= a -> WINf a \/ WrapFreeBCall.IZONE a -> aowned B ly S a \/ (sp0 - ASTACK <= a < sp0)).
{ intros a Ha [Hw|Hz].
- destruct Hw as [Hs|Ht]; [right; exact Hs|].
destruct (WrapFreeBFinn.D_owned_cf B TB ly S _ Hp (proj1 HAR) ASTACK sp0 ltac:(lia) IMGc a Ha (or_introl Ht)) as [O|O]; [left; exact O | right; exact O].
- assert (DIz : WrapFreeBFinn.DI B a) by (unfold WrapFreeBFinn.DI; rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB); exact Hz).
destruct (WrapFreeBFinn.D_owned_cf B TB ly S _ Hp (proj1 HAR) ASTACK sp0 ltac:(lia) IMGc a Ha (or_intror (or_intror DIz))) as [O|O]; [left; exact O | right; exact O]. }
(* ARcf at finit_cf S after the segment's writes (FINH's ARm rebuild, lib/Reusable/YFg3.v) *)
assert (HARF : ARcf tfibsegs B ly (set_internal_inited true S) Hp W memD (with_vm_backing (m_vm_lazy md) mat md)).
{ apply (WrapFreeBFinn.free_finn_ARcf_B B TB ly S Hp W mem md memD mat ASTACK sp0 HAR IMGc).
- unfold ASTACK; lia.
- lia.
- intros a Ha ND. apply aview_same. apply MEQ; rewrite unsigned_lit_small by exact Ha.
+ intros [X|X]; apply ND; unfold WrapFreeBFinn.D, WrapFreeBFinn.DS, WrapFreeBFinn.DT; [right; left; exact X | left; exact X].
+ intros X. apply ND. right; right. unfold WrapFreeBCall.IZONE in X. unfold WrapFreeBFinn.DI. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB). exact X.
- intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (memD x); discriminate|].
destruct (memD x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
assert (NIMG : ~ (YImgTop.IMG_LO_B <= a' < YImgTop.IMG_TOP_B)).
{ intros X. apply (tfib_rom_all a' X). rewrite Ex. exact ROM. }
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False).
{ intros m [_ [bb Hb]] Hm. rewrite Ex in Hb. congruence. }
destruct (EM (sp0 - ASTACK) sp0 a') as [C1|C1]. { exact (PRX memD (PRES a' C1) E'). }
destruct (EM (ly_T ly + t_unwinding) (ly_T ly + t_unwinding + 1) a') as [C2|C2].
{ pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
replace (ly_T ly + t_unwinding) with a' in U by lia. rewrite Ex, Hx, E', ROM in U. discriminate. }
destruct (EM TFIB_IAL_LO TFIB_IAL_HI a') as [C4|C4]; [apply NIMG; unfold TFIB_IAL_LO, TFIB_IAL_HI in C4; lia|].
destruct (EM TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) a') as [C5|C5]; [apply NIMG; unfold TFIB_IAL_FLAG in C5; lia|].
rewrite (MEQ x) in E'; [congruence | |].
+ intros [X|X]; [apply C1 | apply C2]; exact X.
+ unfold WrapFreeBCall.IZONE. tauto.
- rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). exact (vm_aview_f _ _ _ _ _ 0 UNW ltac:(lia)).
- unfold WrapFreeBCall.IAL_POST in IP. cbv zeta in IP. destruct IP as (I1 & I2 & I3 & I4 & I5).
unfold ialloc_cells, ialloc_zero. change (st_internal_inited (set_internal_inited true S)) with true. rewrite (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB).
split.
+ apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (vm_aview_f _ _ _ _ _ 0 I1). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros kk Hkk. destruct kk; [|lia]. apply (vm_aview_f _ _ _ _ _ 0 I2). lia. }
apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO)) with TFIB_IAL_W by lia.
intros kk Hkk. exact (vm_aview_f _ _ _ _ _ kk I3 Hkk). }
apply Forall_cons; [|apply Forall_nil]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 8)) with (TFIB_IAL_W + 8) by lia.
replace (TFIB_IAL_LO + (TFIB_IAL_W - TFIB_IAL_LO + 16)) with (TFIB_IAL_W + 16) by lia.
intros kk Hkk. exact (vm_aview_f _ _ _ _ _ kk I4 Hkk). }
+ assert (ZR : forall a0, TFIB_IAL_LO <= a0 < TFIB_IAL_W \/ TFIB_IAL_W + 16 <= a0 < TFIB_IAL_HI -> aview tfibsegs (w_H W) memD a0 = Some 0).
{ intros a0 Ha0'. unfold aview. rewrite (I5 a0 Ha0'). reflexivity. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TB); apply ZR; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia.
- apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfibsegs (w_H W) mem)); [exact (proj1 (Forall_forall _ _) (amc_const B ly S Hp _ (proj1 HAR)) c Hc)|].
intros i Hi. destruct (proj1 (Forall_forall _ _) CO c Hc i Hi) as (X1 & X2 & X3). apply aview_same.
apply (MEQ (Z_to_bv 64 _)); rewrite unsigned_lit_small by exact X3; [exact X1 | exact X2].
- intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh _]; fold x in Hh; rewrite Hx in Hh; discriminate).
assert (C1 : ~ (sp0 - ASTACK <= a < sp0)) by (intros C1; exact (PRX memD (PRES a C1))).
assert (C2 : ~ (ly_T ly + t_unwinding <= a < ly_T ly + t_unwinding + 1)).
{ intros C2. pose proof (UNW 0%nat ltac:(lia)) as U. rewrite Z.add_0_r in U. unfold mbyte, mrestrict in U.
replace (ly_T ly + t_unwinding) with a in U by lia.
rewrite (seg_rom_none_high a ltac:(clear - Ha; unfold TFIB_IMG_END, kLowShadowBeg, kHighShadowEnd, YImgTop.IMG_TOP_B in *; lia)) in U. fold x in U. rewrite Hx in U. discriminate. }
apply (MEQ x); rewrite Ux.
+ intros [X|X]; [apply C1 | apply C2]; exact X.
+ unfold WrapFreeBCall.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. clear - Ha. unfold kLowShadowBeg in Ha. lia. }
(* the memory frame outside the owned set and the caller's scratch, raw *)
assert (KEEPR : forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> memD x = mem x).
{ intros x NO NS. pose proof (u64_range x) as Ux. apply MEQ.
- intros Hw. destruct (OWN _ (proj1 Ux) (or_introl Hw)) as [O|O]; [exact (NO O) | exact (NS O)].
- intros Hz. destruct (OWN _ (proj1 Ux) (or_intror Hz)) as [O|O]; [exact (NO O) | exact (NS O)]. }
exists TFIB_INST, (sp0 - 2128), (sp0 - 2112), regsD, memD, (with_vm_backing (m_vm_lazy md) mat md).
assert (SA : spZ regsD = sp0 - 2128) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; clear - Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
split. { unfold cfg_at. rewrite HpcD. reflexivity. }
split.
{ unfold free_dpre_cf, DeallocG.dealloc_pre.
split.
{ apply YGcfInstBase.ARXq_cf_intro; [|exact (proj1 QM)].
apply YGcfInstBase.ARX_cf_start.
- exact (eq_sym (ts_inst B TB)).
- exact HARF.
- exact (YGcfXs.ARcf_xsm _ _ _ _ _ _ _ _ HARF). }
split; [exact RP|].
split. { rewrite R1. apply YK0s.ret_ok_even. reflexivity. }
split. { unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold B_INTERCEPTOR_FREE_PC; lia). unfold B_INTERCEPTOR_FREE_PC; lia. }
rewrite SA. unfold DeallocG.DFSTACK_G.
split. { replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
split. { clear - Hlo. unfold ASTACK in *. lia. }
split. { clear - Hbot. lia. }
split. { lia. }
split. { intros a Ha. apply PRES. clear - Ha. unfold ASTACK. lia. }
split. { rewrite R3. exact Hgp. }
split. { rewrite R4, (ts_tp B TB). reflexivity. }
split. { exact R10. }
split. { rewrite R11. exact Ha0. }
split. { exact R12. }
split. { exact R13. }
split. { exact R14. }
split. { exact R15. }
split. { lia. }
split. { clear - Hhi. lia. }
split. { clear - Hal. replace (sp0 - 2128) with (sp0 + (-266) * 8) by lia. rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [lia | exact Hal]. }
split. { lia. }
split. { clear - Hhi. lia. }
split. { clear - Hal. replace (sp0 - 2112) with (sp0 + (-264) * 8) by lia. rewrite Z_mod_plus_full. apply (mod0_factor _ 8 2); [lia | exact Hal]. }
split. { exact LEN. }
split. { exact OBJ0. }
split. { eapply val_mem_addr; [exact OBJ1 | lia]. }
split. { exact TRA. }
split. { unfold ftr_cf in Htr. rewrite (ts_code B TB) in Htr. exact Htr. }
split. { exact Hpn. }
exact Hnh. }
split. { apply same_io_wvb_f. }
split. { unfold RGtop.rin. rewrite SA. unfold spZ. fold sp0. unfold DeallocG.DFSTACK_G, ASTACK. lia. }
split.
{ split; [|split].
- intros a Ha NO NS. apply aview_same. apply KEEPR; rewrite unsigned_lit_small by exact Ha; [exact NO|]. intros X. apply NS. left. unfold spZ. fold sp0. exact X.
- intros x NO NS. apply KEEPR; [exact NO|]. intros X. apply NS. left. unfold spZ. fold sp0. exact X.
- intros (Mi & Mt). pose proof (u64_range) as UR.
assert (CASES : forall x : word, memD x = mem x \/ (sp0 - ASTACK <= bv_unsigned x < sp0) \/ WrapFreeBCall.IZONE (bv_unsigned x)).
{ intros x. destruct (EM (sp0 - ASTACK) sp0 (bv_unsigned x)) as [C1|C1]; [right; left; exact C1|].
destruct (EM TFIB_IAL_LO TFIB_IAL_HI (bv_unsigned x)) as [C4|C4]; [right; right; left; exact C4|].
destruct (EM TFIB_IAL_FLAG (TFIB_IAL_FLAG + 4) (bv_unsigned x)) as [C5|C5]; [right; right; right; exact C5|].
destruct (EM (ly_T ly + t_unwinding) (ly_T ly + t_unwinding + 1) (bv_unsigned x)) as [C2|C2].
- left. assert (Ex : x = Z_to_bv 64 (ly_T ly + t_unwinding)) by (replace (ly_T ly + t_unwinding) with (bv_unsigned x) by lia; symmetry; apply Z_to_bv_bv_unsigned). rewrite Ex. exact TRAW.
- left. apply MEQ; [intros [X|X]; [exact (C1 X) | exact (C2 X)] | unfold WrapFreeBCall.IZONE; tauto]. }
split; intros x b E.
+ destruct (CASES x) as [Eq|[C1|C4]].
* rewrite Eq in E. exact (Mi x b E).
* unfold YAkMemnorm.ro_addr. rewrite tfib_find_segment_none_high; [reflexivity|]. clear - C1 Hlo T7. unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *. lia.
* apply ro_img_rw_f. unfold WrapFreeBCall.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in C4. lia.
+ destruct (CASES x) as [Eq|[C1|C4]].
* rewrite Eq in E. exact (Mt x b E).
* right. clear - C1 Hhi T4. unfold TASK_SIZE, kHighMemEnd in *. lia.
* right. unfold WrapFreeBCall.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in C4. unfold TASK_SIZE. lia. }
split. { intros i Hi. rewrite (ts_errno B TB). apply MEQ; unfold w64; rewrite unsigned_lit_small by (unfold TFIB_ERRNO; lia).
- apply notWIN_img_f. unfold TFIB_ERRNO, TFIB_IMG_LO, TFIB_IMG_END, YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B. lia.
- unfold WrapFreeBCall.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_ERRNO. lia. }
unfold K_F, spZ, raZ, s0Z. fold sp0.
split; [reflexivity|]. split; [exact R2|]. split; [exact R1|]. split; [exact R8|]. split; [exact R3|].
split; [rewrite R4, Htp, (ts_tp B TB); reflexivity|]. split; [exact RS|].
split; [exact V1|]. split; [exact V8|]. split; [exact V9|].
split; [exact V18|]. split; [exact V19|]. split; [exact V20|]. split; [exact V21|]. exact PRES.
Qed.
End e.

Theorem wf_call_B : wf_call_stmt tfibsegs B 1 ARXB K_F.
Proof. intros ly S Hp W regs mem md p n ch FEN RP. eapply wf_call_at; eassumption. Qed.
End k.
End c.
