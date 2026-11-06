(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/WrapMallocAM1.v, with its module paths changed; 12 of its 171 lines of code are new or changed and 6 lines of the source are left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image A (asan, pin 1be0f53d96cb), field M1 of a Theorem Labs lane's Record
   wrap_malloc_walk_cf (lib/Reusable/YGcfMallocCompose.v:153, blob e929a4c12d5b) as its CORRECTED twin
   wm_call_stmt_FIX_A (below: one premise added, and why), with
     segs := tfibsegs, al := 8, atp := 1 (FROM_MALLOC), acf := 1 (can_fill), ARX := ARXh_A B, K := K_A
     (lib/A/WrapMallocADefs.v),
   and the image facts as premises: TfibSyms B, the unwinder's spec U1 (AFl0.v:23, discharged by A's
   tfib_unwind_ok) and cf_pc_allocate = PC_ALLOCATE (A 0x325b8, CfImgA.v:40). The run is WrapMallocACall.seg_call;
   this file reads no instruction. The image-A twin of a Theorem Labs lane's lib/AU/WrapMallocBM1.v, same proof.
   ARcf after the segment: AR_frame_law_ok_cf (YG0qcf.v:667) on the segment's frame (the caller's stack window,
   which AR_stack_law_cf keeps unowned, and T + t_unwinding, which reads 0 again). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AllocG RGtop YGcfRmodel YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import WrapAKit WrapMallocASeed WrapMallocACall WrapMallocADefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma wvb_self_m : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_wvb_m : forall md mat, same_io md (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat. unfold same_io. destruct md; cbn; repeat split; reflexivity. Qed.

(* One byte read on two memories: the same byte. *)
Lemma vm1_mbyte : forall (segs : list Segment) m1 m2 a v, val_mem segs m1 a 1 v -> val_mem segs m2 a 1 v -> mbyte segs m1 a = mbyte segs m2 a.
Proof. intros segs m1 m2 a v H1 H2. pose proof (H1 0%nat ltac:(lia)) as E1. pose proof (H2 0%nat ltac:(lia)) as E2. rewrite Z.add_0_r in E1, E2. congruence. Qed.
(* A byte read on the restricted memory off the image is the raw byte. *)
Lemma vm1_raw : forall (H : word -> bool) m a v, val_mem tfibsegs (mrestrict H m) a 1 v -> off_img a ->
m (Z_to_bv 64 a) = Some (Z_to_bv 8 (le_byte v 1 0)).
Proof.
intros H m a v Hv Ha. pose proof (Hv 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E. unfold mbyte, mrestrict in E.
destruct (H (Z_to_bv 64 a)); [rewrite (seg_rom_none_off a Ha) in E; discriminate|].
destruct (m (Z_to_bv 64 a)); [exact E | rewrite (seg_rom_none_off a Ha) in E; discriminate].
Qed.
Lemma apresent_aview_m : forall (H : word -> bool) m a, apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Section k.
Variable B : asyms.

Hypothesis TB : TfibSyms B.
Hypothesis U1 : tfib_unwind_spec.
Hypothesis Hpc : cf_pc_allocate = PC_ALLOCATE.
(* a Theorem Labs lane, 14:40Z: ARcf will imply xs_placed_cf once a8 appends the field to ARmcf (YG0ncf.v); until then the
   walk takes it as this hypothesis, with exactly this statement. *)
Hypothesis xs_placed_of_ARcf_H :
forall ly S Hp W mem md, ARcf tfibsegs B ly S Hp W mem md -> xs_placed_cf ly S.

(* ---------------------------------------------------------------------------- *)
(* The corrected twin of the record's field M1 (function-proving section 4). The record's wm_call
   (lib/Reusable/YGcfMallocCompose.v:153-161) is NOT provable as stated: its conclusion asks AllocG.alloc_pre at
   Allocate's entry, whose conjunct `ly_bot ly < spZ regsA` (Reusable/AllocG.v:75) is about the sp AFTER the
   interceptor's 2032 + 96 bytes and asan_malloc's 16, i.e. spZ regs - 2144; the premises give only
   `ly_bot ly < spZ regs` (acall_pre_cf, YG0dcf.v:52) and `ly_stk_lo ly + ASTACK <= spZ regs`, and layout_ok gives
   only `ly_stk_lo ly <= ly_bot ly` (YG0f.v:322), so a caller sp with ly_bot ly = spZ regs - 1 meets every premise
   and misses the conjunct. a Theorem Labs lane reached the same on image B (AU/WrapMallocBStmt.v:190-195 wm_call_stmt_FIX,
   premise (2)). The added premise is stated EXACTLY as the coming engine fix gives it (a Theorem Labs lane 16:03Z, from
   a Theorem Labs lane 15:49Z): `ly_bot ly + ACALL_PREFIX < spZ regs` with ACALL_PREFIX := 4096, written here as the
   numeral, so that the swap is by lia. It suffices: alloc_pre asks ly_bot ly < spZ regsA = spZ regs - 2144, and
   2144 < 4096. The other FIX premise B needed,
   xs_placed_cf ly S, is NOT added here: it comes from the Section hypothesis xs_placed_of_ARcf_H (a Theorem Labs lane's
   decision of 14:40Z), which a8's coming ARcf field makes a lemma. *)
Definition wm_call_stmt_FIX_A (al atp acf : Z) (ARX : ARXh_t tfibsegs) (K : Kmalloc_t tfibsegs) : Prop :=
forall ly S Hp W regs mem md n ch,
  mentry_cf tfibsegs B ly S Hp W regs mem md n ch -> YGcfRmodel.rpre_cfr B S n -> 0 <= n < cf_malloc_max ->
  ly_bot ly + 4096 < spZ regs ->
  SRr tfibsegs W (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md)
  (fun W1 c1 => exists inst so bp regsA memA mdA,
    c1 = cfg_at tfibsegs cf_pc_allocate regsA memA mdA /\
    malloc_apre_cf tfibsegs B cf_malloc_max al atp acf ARX Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf B ly regs ch) /\
    same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
    YGcfMallocComposeKeep.ikeep_mn_cf tfibsegs B ly S regs W mem W1 memA /\ errno_kept_cf B mem memA /\
    K ly S Hp W regs mem md n ch W1 regsA memA mdA).

Theorem wm_call_FIX_A : wm_call_stmt_FIX_A 8 1 1 (ARXh_A B) K_A.
Proof.
intros ly S Hp W regs mem md n ch MEN RP HN BOT.
pose proof (xs_placed_of_ARcf_H ly S Hp W mem md (proj1 (proj1 MEN))) as XSP.
pose proof MEN as (PRE & Hn & Hnmax & Hlive & Htr).
pose proof PRE as (HAR & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & QM & SL & ER & AB & BR & HUL & ARO).
unfold spZ, raZ in Hal, Hlo, Hbot, Hhi, HPRES, BOT.
set (sp0 := bv_unsigned (getr regs 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof (cf_layout B ly S Hp _ _ (proj1 HAR)) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (lo_stk_ceil ly LO) as SC.
pose proof (LYB B ly S Hp W regs mem md ch PRE) as LB.
pose proof (stack_ivs B ly S Hp W regs mem md ch PRE) as (IT & _).
assert (NT : forall a, sp0 - ASTACK <= a < sp0 -> ~ (ly_T ly + t_unwinding <= a < ly_T ly + t_unwinding + 1)).
{ intros a Ha Ht. clear - Ha Ht IT. unfold kThreadObjSize, t_unwinding, ASTACK in *. lia. }
assert (UNW0 : val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0) by exact (cf_unwinding_val B ly S Hp (w_H W) mem (proj1 HAR)).
assert (OFFT : off_img (ly_T ly + t_unwinding)).
{ apply (zone3_off_img _ _ _ (proj1 LB)). unfold kThreadObjSize, t_unwinding. lia. }
destruct (AR_laws_ok_cf tfibsegs B) as [Lb Lsh Lz Lfr Lfrs Lfl Lc Lst Lw Lly Lol Loi Lsep Lci Lhf].
unfold mtr_cf. rewrite (ts_code B TB) in *. cbn [pc_wrap_malloc pc_malloc_ra0 Tfib_code] in *.
unfold cfg_at. rewrite <- (wvb_self_m md) at 1.
eapply SRr_mono; [exact (seg_call B TB ly S Hp W regs mem md ch (m_vm_materialized md) PRE U1) |].
intros W' c' _ (-> & regsA & memA & mat & -> & R1 & R2 & R10 & R11 & R12 & R13 & R14 & R15 & R8 & R9 & R3 & R4 & RS
& MEQ & UNW & PRES & OBJ0 & OBJ1 & TRA & V1 & V8 & V9 & V18 & V19 & V20 & V21 & VA0 & VA1).
fold sp0 in R2, R13, MEQ, PRES, OBJ0, OBJ1, TRA, V1, V8, V9, V18, V19, V20, V21, VA0, VA1.
assert (LEN : (1 <= length (call_trace ly (pc_malloc_ra0 Tfib_code) regs ch) <= 30)%nat).
{ unfold call_trace. destruct (frame0_ok ly regs); [apply unwind_of_chain_length | cbn; lia]. }
(* the T + t_unwinding byte, raw and on the view *)
assert (TRAW : memA (Z_to_bv 64 (ly_T ly + t_unwinding)) = mem (Z_to_bv 64 (ly_T ly + t_unwinding))).
{ rewrite (vm1_raw _ _ _ _ UNW OFFT), (vm1_raw _ _ _ _ UNW0 OFFT). reflexivity. }
(* the segment's raw frame: outside the caller's stack window *)
assert (MEQ2 : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0) -> memA x = mem x).
{ intros x X. destruct (Z_lt_le_dec (bv_unsigned x) (ly_T ly + t_unwinding)) as [Y|Y];
[|destruct (Z_lt_le_dec (bv_unsigned x) (ly_T ly + t_unwinding + 1)) as [Y'|Y']].
- apply MEQ; [exact X | lia].
- assert (Ex : x = Z_to_bv 64 (ly_T ly + t_unwinding)) by (replace (ly_T ly + t_unwinding) with (bv_unsigned x) by lia; symmetry; apply Z_to_bv_bv_unsigned). rewrite Ex. exact TRAW.
- apply MEQ; [exact X | lia]. }
assert (MEQV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ASTACK <= a < sp0) -> aview tfibsegs (w_H W) memA a = aview tfibsegs (w_H W) mem a).
{ intros a Ha X. apply aview_same. apply MEQ2. rewrite unsigned_lit_small by exact Ha. exact X. }
exists TFIB_INST, (sp0 - 2128), (sp0 - 2112), regsA, memA, (with_vm_backing (m_vm_lazy md) mat md).
split. { unfold cfg_at. rewrite Hpc. reflexivity. }
split.
{ unfold malloc_apre_cf, AllocG.alloc_pre.
split.
{ unfold ARXh_A. split; [symmetry; exact (ts_inst B TB)|].
split.
{ apply (Lfr ly S Hp W mem md memA (with_vm_backing (m_vm_lazy md) mat md) HAR).
- intros a Ha Ow. apply MEQV; [exact Ha|]. intros X. apply (Lst ly S Hp W mem md a HAR); [clear - X Hlo Hhi; unfold ASTACK in *; lia | exact Ow].
- intros a Hv. unfold aview, mbyte, mrestrict in Hv |- *. set (x := Z_to_bv 64 a) in *.
destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - ASTACK)) as [A|A]; [|destruct (Z_lt_le_dec (bv_unsigned x) sp0) as [A'|A']].
+ rewrite (MEQ2 x ltac:(lia)). exact Hv.
+ pose proof (PRES (bv_unsigned x) ltac:(lia)) as [Hh [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hh, Hb. rewrite Hh, Hb. discriminate.
+ rewrite (MEQ2 x ltac:(lia)). exact Hv.
- reflexivity.
- reflexivity.
- reflexivity.
- intros a Hb Hh. apply MEQ2. unfold w64. rewrite unsigned_lit_small by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb; lia).
clear - Hb Hlo T7. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. lia. }
split; [exact QM|]. split; [exact SL|]. split; [exact ER|]. split; [exact AB|]. split; [exact BR|]. exact XSP. }
split; [exact RP|].
split. { rewrite R1. apply YK0s.ret_ok_even. reflexivity. }
split. { unfold raZ. rewrite R1. unfold w64, RA_ALLOC, tfib_A__ZN6__asan11asan_mallocEmPN11__sanitizer18BufferedStackTraceE.
rewrite unsigned_lit_small by lia. lia. }
assert (SA : spZ regsA = sp0 - 2144) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; clear - Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
rewrite SA. unfold AllocG.AFSTACK_G.
split. { replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
split. { clear - Hlo. unfold ASTACK in *. lia. }
split. { clear - BOT. lia. }
split. { lia. }
split. { intros a Ha. apply PRES. clear - Ha. unfold ASTACK. lia. }
split. { rewrite R3. exact Hgp. }
split. { rewrite R4, (ts_tp B TB). reflexivity. }
split. { exact R10. }
split. { rewrite R11. exact Hn. }
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
split. { unfold mtr_cf in Htr. rewrite (ts_code B TB) in Htr. exact Htr. }
split. { exact Hnmax. }
exact Hlive. }
split. { apply same_io_wvb_m. }
split. { unfold RGtop.rin, spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by (clear - Usp Hlo T7; unfold ASTACK, kHighMemBeg in *; lia).
fold sp0. unfold AllocG.AFSTACK_G, ASTACK. lia. }
split.
{ split; [|split].
- intros a Ha NO NS. apply MEQV; [exact Ha|]. intros X. apply NS. left. unfold spZ. fold sp0. exact X.
- intros x NO NS. apply MEQ2. intros X. apply NS. left. unfold spZ. fold sp0. exact X.
- intros MN. apply (YAkMemnorm.memnorm_frame_off_segs tfibsegs mem memA (sp0 - ASTACK) sp0 MN).
+ intros x [X|X]; apply MEQ2; lia.
+ clear - Hhi T4. unfold kHighMemEnd in *. unfold TASK_SIZE. lia.
+ intros x X. apply tfib_find_segment_none_high. clear - X Hlo T7. unfold TFIB_IMG_END, ASTACK, kHighMemBeg in *. lia. }
split. { intros i Hi. rewrite (ts_errno B TB). apply MEQ2. unfold w64. rewrite unsigned_lit_small by (unfold TFIB_ERRNO; lia).
clear - Hi Hlo T7. unfold TFIB_ERRNO, ASTACK, kHighMemBeg in *. lia. }
unfold K_A, spZ, raZ, s0Z. fold sp0.
split; [reflexivity|]. split; [exact R2|]. split; [exact R1|]. split; [exact R8|]. split; [exact R3|].
split; [rewrite R4, Htp, (ts_tp B TB); reflexivity|]. split; [exact RS|].
split; [exact VA0|]. split; [exact VA1|]. split; [exact V1|]. split; [exact V8|]. split; [exact V9|].
split; [exact V18|]. split; [exact V19|]. split; [exact V20|]. split; [exact V21|]. exact PRES.
Qed.
End k.
End c.
