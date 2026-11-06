(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/WrapMallocARet.v, with its module paths changed; 75 of its 315 lines of code are new or changed and 171 lines of the source are left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image A (asan, pin 1be0f53d96cb), field M2 (wm_ret) of
   a Theorem Labs lane's Record wrap_malloc_walk_cf (lib/Reusable/YGcfMallocCompose.v:165, blob e929a4c12d5b) at
   ARX := ARXh_A B, K := K_A (lib/A/WrapMallocADefs.v): Allocate's return (RA_ALLOC) -> __wrap_malloc's return.
   The machine runs are WrapMallocARetM.m_null / m_blk; this file is the allocator-side glue, by the method of
   plugin-hostd/fuzz_reply's lib/A/RGthinS6.v rt_seg_npost (a working branch 66a127cb11e): the same
   SRr / RGtop framework. Rule 24 and the relocation check: the internal file RULE24-W6PRE.md.
   What the glue does:
   - the stack is not in AOXm_cf at either layout (AR_stack_law_ok_cf for aowned; xs_placed_cf's disjointness from
     the stack extent, static_extents ly's index 8, for xs_cf), so AllocG.alloc_post's frame carries K's frame words
     and the caller's window from memA to mem2;
   - on a block, malloc_cf_apath_success (YGcfApath.v:38) puts (q, n) in blocks S2 and block_user_range_cf
     (YGcfBlockRange.v:31) puts it below ASAN_CEIL, hence off the stack and non-zero;
   - after the run, ARcf at mem' by AR_frame_law_ok_cf (YG0qcf.v:667): the run writes only the caller's stack window
     and errno, neither owned (errno is inside the image and not in Tfib_owned_static), and neither in_band_rw.
   No Admitted / Axiom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfRoom YG0scf YG0qcf YG0lawscf YGcfApath YGcfBlockRange.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import AllocG RGtop YGcfRmodel YAkMemnorm YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB13 AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w WrapMallocACall WrapMallocARetM WrapMallocADefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import WrapMallocARetH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The callee-saved registers, one goal per register (RGthinS.v:34-55). *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section b.
Variable segs0 : list Segment.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (nmax al atp acf : Z).
Let errno_not_owned_A := errno_not_owned_A B TB.

Theorem wm_ret_A : forall ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
  mentry_cf tfibsegs B ly S Hp W regs mem md n ch ->
  K_A ly S Hp W regs mem md n ch W1 regsA memA mdA ->
  malloc_apre_cf tfibsegs B nmax al atp acf (ARXh_A B) Hp inst so bp ly S W1 regsA memA mdA n (mtr_cf B ly regs ch) ->
  malloc_apost_cf tfibsegs B (ARXh_A B) Hp inst ly S W1 regsA memA mdA
    (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 q) -> qtight S2 ->
  (exists trc, apath (malloc_cf n (mtr_cf B ly regs ch) S) trc (q, S2) /\ gflag trc = true) ->
  (q = PNull -> val_mem tfibsegs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1) ->
  SRr tfibsegs W2 (cfg_at tfibsegs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARXh_A B Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep tfibsegs B regs W2 mem2 W' mem' /\ RGtop.rwin tfibsegs regs W' mem' /\
    (YAkMemnorm.memnorm tfibsegs mem2 -> YAkMemnorm.memnorm tfibsegs mem') /\
    (q <> PNull -> errno_kept_cf B mem2 mem') /\
    (q = PNull -> rd32 (aview tfibsegs (w_H W') mem') (as_errno B) 12 /\ aview tfibsegs (w_H W') mem' (as_oom_byte B) = Some 1)).
Proof.
intros ly S Hp W regs mem md n ch W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2 MEN HK APR APO A02 LP2 PATH OOM.
pose proof MEN as (PRE & Hn & Hnmax & Hlive & Htr).
pose proof PRE as (HAR & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & QM & SL & ER & AB & BR & HUL & ARO).
unfold K_A in HK. unfold spZ, raZ, s0Z in *.
set (sp0 := bv_unsigned (getr regs 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HK as (EW1 & KSP & K1ra & K8 & K3 & K4 & KS & F0 & F1 & FRA & FS0 & FS1 & FS2 & FS3 & FS4 & FS5 & KW).
subst W1.
pose proof (proj1 APR) as ARX1.
pose proof APO as (ARX2 & LLE & WLE & PRS & SIO & FR2 & FR2w & PR2).
pose proof ARX1 as (Hinst & AR1 & _).
pose proof ARX2 as (_ & AR2 & _ & _ & _ & _ & _ & XSP2).
pose proof (amc_layout _ _ _ _ _ (proj1 AR1)) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
assert (THI : ly_stk_hi ly <= kHighMemEnd) by exact T4.
assert (TLO : kHighMemBeg <= ly_stk_lo ly) by exact T7.
pose proof (lo_stk_ceil ly LO) as SC.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
destruct LLE as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the stack is in neither AOXm_cf *)
assert (NOWN1 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOXm_cf B ly S a).
{ intros a Ha [OW|EX].
  - exact (AR_stack_law_ok_cf tfibsegs B ly S Hp W memA mdA a AR1 Ha OW).
  - pose proof (proj1 APR) as ARX1'. destruct ARX1' as (_ & _ & _ & _ & _ & _ & _ & XSP1).
    unfold xs_placed_cf in XSP1. apply Exists_exists in EX as (e & He & Hin).
    pose proof (proj1 (Forall_forall _ _) XSP1 e He) as (_ & _ & _ & DJ).
    pose proof (proj1 (Forall_forall _ _) DJ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)
      ltac:(rewrite !in_app_iff; right; left; unfold static_extents; rewrite in_app_iff; right; left; reflexivity)) as D.
    unfold zdisjoint, in_zr in *. cbn [fst snd] in *. lia. }
assert (NOWN2 : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOXm_cf B ly2 S2 a).
{ intros a Ha [OW|EX].
  - apply (AR_stack_law_ok_cf tfibsegs B ly2 S2 Hp W2 mem2 md2 a AR2); [rewrite Eslo, Eshi; exact Ha | exact OW].
  - unfold xs_placed_cf in XSP2. apply Exists_exists in EX as (e & He & Hin).
    pose proof (proj1 (Forall_forall _ _) XSP2 e He) as (_ & _ & _ & DJ).
    pose proof (proj1 (Forall_forall _ _) DJ (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2)
      ltac:(rewrite !in_app_iff; right; left; unfold static_extents; rewrite in_app_iff; right; left; reflexivity)) as D.
    unfold zdisjoint, in_zr in *. cbn [fst snd] in *. rewrite Eslo, Eshi in D. lia. }
(* the block, when there is one: in blocks S2 and below ASAN_CEIL *)
assert (QB : q <> PNull -> In (q, n) (blocks S2)).
{ intros HQ. destruct PATH as (trc & HP & HG).
  destruct (malloc_cf_apath_success (as_universe B) S n (mtr_cf B ly regs ch) trc q S2
    (amc_universe _ _ _ _ _ (proj1 HAR)) (amc_wf _ _ _ _ _ (proj1 HAR)) ltac:(lia) Hlive Htr SL ER BR HP HQ)
    as (_ & _ & _ & _ & EB & _).
  rewrite EB. apply in_or_app. right. left. reflexivity. }
assert (QR : q <> PNull -> 4096 + 16 <= sptr_addr B ly2 q /\ sptr_addr B ly2 q + req_size n <= ASAN_CEIL).
{ intros HQ. destruct (block_user_range_cf tfibsegs B ly2 S2 Hp W2 mem2 md2 q n AR2 (QB HQ)) as (_ & [[X1 X2]|[X1 X2]]).
  - unfold kLowShadowBeg in X2. split; lia.
  - unfold kHighMemBeg in X1. split; lia. }
assert (NE : forall a, ASAN_CEIL <= a -> ~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)).
{ intros a Ha [HQ Hin]. destruct (QR HQ) as [_ X2]. lia. }
(* the frame from memA to mem2 on the caller's stack, outside Allocate's own window *)
assert (STKV : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp0 - 2144 - AllocG.AFSTACK_G <= a < sp0 - 2144) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memA a).
{ intros a Ha Hn2. apply FR2.
  - unfold kHighMemBeg, kHighMemEnd in *. lia.
  - exact (NOWN1 a Ha).
  - exact (NOWN2 a Ha).
  - unfold ascratch. rewrite (ts_errno B TB). unfold spZ. rewrite KSP. unfold w64.
    rewrite YP03.unsigned_lit_small by (unfold ASTACK, kHighMemBeg in *; lia).
    intros [X|X]; [unfold AllocG.AFSTACK_G in *; lia
    | unfold TFIB_ERRNO in X; lia].
  - apply NE. lia. }
assert (XF : forall a v, ly_stk_lo ly <= a -> a + 8 <= ly_stk_hi ly -> sp0 - 2144 <= a ->
  val_mem tfibsegs (mrestrict (w_H W) memA) a 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v H1 H2 H3 V. apply (val_mem_xfer_r (w_H W) (w_H W2) memA mem2 a 8 v); [|exact V].
  intros k Hk. apply STKV; [lia|]. unfold AllocG.AFSTACK_G. lia. }
assert (PW2 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W2) mem2 a).
{ intros a Ha. destruct (Z_le_gt_dec (sp0 - 2144) a) as [L|L]; [|destruct (Z_le_gt_dec (sp0 - 2144 - AllocG.AFSTACK_G) a) as [L2|L2]].
  - apply vis_apresent_hi_r; [unfold TFIB_IMG_END; unfold ASTACK, kHighMemBeg in *; lia|].
    rewrite STKV by (unfold ASTACK in *; lia). apply apresent_vis_r. apply KW. unfold spZ. fold sp0. lia.
  - apply PR2. unfold spZ. rewrite KSP. unfold w64.
    rewrite YP03.unsigned_lit_small by (unfold ASTACK, kHighMemBeg in *; lia). lia.
  - apply vis_apresent_hi_r; [unfold TFIB_IMG_END; unfold ASTACK, kHighMemBeg in *; lia|].
    rewrite STKV by (unfold ASTACK, AllocG.AFSTACK_G in *; lia).
    apply apresent_vis_r. apply KW. unfold spZ. fold sp0. lia. }
assert (SP2 : bv_unsigned (getr regs2 2) = sp0 - 2144).
{ rewrite (ap_get_r regsA regs2 2 2%bv PRS ltac:(unfold acallee_saved; lia) eq_refl), KSP. unfold w64.
  apply YP03.unsigned_lit_small. unfold ASTACK, kHighMemBeg in *. lia. }
assert (G4 : getr regs2 4 = w64 TFIB_TP).
{ rewrite (ap_get_r regsA regs2 4 4%bv PRS ltac:(unfold acallee_saved; lia) eq_refl), K4, Htp, (ts_tp B TB). reflexivity. }
assert (RAA : bv_unsigned (getr regsA 1) = RA_ALLOC).
{ rewrite K1ra. unfold w64. apply YP03.unsigned_lit_small.
  unfold RA_ALLOC, tfib_A__ZN6__asan11asan_mallocEmPN11__sanitizer18BufferedStackTraceE. lia. }
(* the frames at the run's sp = sp0 - 2144 *)
assert (AFR : afr_okm W2 mem2 (sp0 - 2144) (bv_unsigned (getr regs 2))).
{ split.
  - apply XF; [unfold ASTACK in *; lia | lia | lia |].
    eapply val_mem_addr_m; [exact F0 | unfold spZ; fold sp0; lia].
  - apply XF; [unfold ASTACK in *; lia | lia | lia |].
    eapply val_mem_addr_m; [exact F1 | unfold spZ; fold sp0; lia]. }
assert (IFR : ifr_okm W2 mem2 (sp0 - 2144 + IFR_OFF) (raZ regs) (s0Z regs) (bv_unsigned (getr regs 9))
  (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))).
{ unfold ifr_okm, IFR_OFF. repeat split;
  (apply XF; [unfold ASTACK in *; lia | lia | lia |];
   eapply val_mem_addr_m; [eassumption | unfold spZ; fold sp0; lia]). }
assert (RNG : Forall (fun v => 0 <= v < 2 ^ 64) [raZ regs; s0Z regs; bv_unsigned (getr regs 9);
  bv_unsigned (getr regs 18); bv_unsigned (getr regs 19); bv_unsigned (getr regs 20); bv_unsigned (getr regs 21);
  bv_unsigned (getr regs 2)])
  by (repeat (apply Forall_cons; [first [apply u64_range | unfold raZ, s0Z; apply u64_range]|]); apply Forall_nil).
assert (HRET : YK0s.ret_ok (w64 (raZ regs))) by (unfold raZ; rewrite w64_unsigned_r; exact Hra).
assert (SPLO : TFIB_IMG_END + 16 <= sp0 - 2144) by (unfold ASTACK, TFIB_IMG_END, kHighMemBeg in *; lia).
assert (SPHI : sp0 - 2144 + 2144 <= 2 ^ 64) by lia.
rewrite RAA. unfold cfg_at at 1.
(* the ARcf part of the conclusion, common to both arms: the run writes the stack window and errno only *)
assert (ARCF' : forall mem' mat,
  (forall x : word, ~ (sp0 - 2144 - 16 <= bv_unsigned x < sp0 - 2144) -> ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> mem' x = mem2 x) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W2) mem2 a <> None -> aview tfibsegs (w_H W2) mem' a <> None) ->
  ARcf tfibsegs B ly2 S2 Hp W2 mem' (with_vm_backing (m_vm_lazy md2) mat md2)).
{ intros mem' mat MEQ VIS.
  apply (AR_frame_law_ok_cf tfibsegs B ly2 S2 Hp W2 mem2 md2 mem' (with_vm_backing (m_vm_lazy md2) mat md2) AR2).
  - intros a Ha OW. apply aview_same. apply MEQ.
    + rewrite YP03.unsigned_lit_small by exact Ha. intros X.
      apply (AR_stack_law_ok_cf tfibsegs B ly2 S2 Hp W2 mem2 md2 a AR2); [rewrite Eslo, Eshi; unfold ASTACK in *; lia | exact OW].
    + rewrite YP03.unsigned_lit_small by exact Ha. intros X.
      exact (errno_not_owned_A ly2 S2 Hp W2 mem2 md2 a AR2 X OW).
  - intros a Hv. rewrite aview_mod_r in Hv |- *. apply VIS; [apply Z.mod_pos_bound; lia | exact Hv].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros a Hb _. apply MEQ; unfold w64;
    rewrite YP03.unsigned_lit_small by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb; lia).
    + unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK in *. lia.
    + unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_ERRNO in *. lia. }
destruct (RGtop.rg_null_dec q) as [EQ|HQ].
- (* q = PNull: a0 = 0, errno := ENOMEM *)
  assert (A0 : getr regs2 10 = w64 0)
    by (rewrite A02, EQ; cbn [sptr_addr sptr_exp aeval]; reflexivity).
  eapply SRr_mono.
  { apply (m_null W2 md2 regs2 mem2 (sp0 - 2144) (raZ regs) (s0Z regs) (bv_unsigned (getr regs 9))
      (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))
      (bv_unsigned (getr regs 2))).
    - exact SP2.
    - exact SPLO.
    - exact SPHI.
    - exact A0.
    - exact G4.
    - exact RNG.
    - exact AFR.
    - exact IFR.
    - intros a Ha. apply PW2. unfold ASTACK in *. lia.
    - exact HRET. }
  intros W' c' _ POST. destruct POST as (EW & regs' & mem' & mat & Ec & (MR1 & MR2 & MR3 & MR4) & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G10 & GK).
  subst W' c'.
  exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
  split. { unfold cfg_at. reflexivity. }
  split.
  { apply ap_mk_r. cs_cases.
    - rewrite G2. replace (sp0 - 2144 + 2144) with sp0 by lia. unfold sp0. rewrite w64_unsigned_r. reflexivity.
    - rewrite (GK 3%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 3 3%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact K3.
    - rewrite (GK 4%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 4 4%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact K4.
    - rewrite G8. unfold s0Z. rewrite w64_unsigned_r. reflexivity.
    - rewrite G9, w64_unsigned_r. reflexivity.
    - rewrite G18, w64_unsigned_r. reflexivity.
    - rewrite G19, w64_unsigned_r. reflexivity.
    - rewrite G20, w64_unsigned_r. reflexivity.
    - rewrite G21, w64_unsigned_r. reflexivity.
    - rewrite (GK 22%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 22 22%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 22 ltac:(lia)).
    - rewrite (GK 23%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 23 23%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 23 ltac:(lia)).
    - rewrite (GK 24%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 24 24%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 24 ltac:(lia)).
    - rewrite (GK 25%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 25 25%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 25 ltac:(lia)).
    - rewrite (GK 26%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 26 26%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 26 ltac:(lia)).
    - rewrite (GK 27%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 27 27%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 27 ltac:(lia)). }
  split. { rewrite G10, EQ. cbn [sptr_addr sptr_exp aeval]. reflexivity. }
  split.
  { unfold ARXh_A. split; [exact Hinst|]. split; [|exact (proj2 (proj2 ARX2))].
    apply (ARCF' mem' mat).
    - intros x N1 N2. apply MR1; [exact N1 | exact N2].
    - intros a Ha Hv. exact (MR4 a Ha Hv). }
  split; [apply same_io_wvb_r|].
  split.
  { unfold RGtop.rkeep. split.
    - intros a Ha Hs. apply aview_same. apply MR1.
      + rewrite YP03.unsigned_lit_small by exact Ha. intros X. apply Hs. unfold ascratch. left. unfold spZ. fold sp0.
        unfold ASTACK in *. lia.
      + rewrite YP03.unsigned_lit_small by exact Ha. intros X. apply Hs. unfold ascratch. right. rewrite (ts_errno B TB). exact X.
    - intros x Hs. apply MR1.
      + intros X. apply Hs. unfold ascratch. left. unfold spZ. fold sp0. unfold ASTACK in *. lia.
      + intros X. apply Hs. unfold ascratch. right. rewrite (ts_errno B TB). exact X. }
  split.
  { unfold RGtop.rwin, spZ. intros a Ha. fold sp0 in Ha.
    assert (Ra : 0 <= a < 2 ^ 64) by (unfold ASTACK, kHighMemBeg in *; lia).
    destruct (Z_le_gt_dec (sp0 - 2144) a) as [L|L]; [|destruct (Z_le_gt_dec (sp0 - 2144 - 16) a) as [L2|L2]].
    - apply (apresent_same (w_H W2) mem2 mem' a).
      + apply MR1; rewrite YP03.unsigned_lit_small by exact Ra.
        * lia.
        * unfold TFIB_ERRNO. unfold TFIB_IMG_END in *. lia.
      + apply PW2. unfold ASTACK in *. lia.
    - apply MR3. lia.
    - apply (apresent_same (w_H W2) mem2 mem' a).
      + apply MR1; rewrite YP03.unsigned_lit_small by exact Ra.
        * lia.
        * unfold TFIB_ERRNO. unfold TFIB_IMG_END in *. lia.
      + apply PW2. unfold ASTACK in *. lia. }
  split.
  { intros MN. apply (memnorm_write_r mem2 mem' (sp0 - 2144 - 16) (sp0 - 2144) TFIB_ERRNO MN).
    - exact MR1.
    - intros x Hx. apply (apresent_wview_r (w_H W2) mem2 x). apply PW2. unfold ASTACK in *. lia.
    - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (rw_wr_m mem2 (bv_unsigned x)).
      unfold TFIB_ERRNO in *. lia. }
  split. { intros HQ. exfalso. exact (HQ EQ). }
  intros _. split.
  { rewrite (ts_errno B TB). apply val_mem_rd32_r. exact MR2. }
  { pose proof (OOM EQ) as HO.
    assert (HOV : val_mem tfibsegs (mrestrict (w_H W2) mem') (as_oom_byte B) 1 1).
    { apply (val_mem_raw_r (w_H W2) mem2 mem' (as_oom_byte B) 1 1); [|exact HO].
      intros k Hk. apply MR1; rewrite (ts_oom B TB); rewrite YP03.unsigned_lit_small by (unfold TFIB_OOM; cbn in Hk; lia);
      unfold TFIB_OOM, TFIB_ERRNO; cbn in Hk; [unfold TFIB_IMG_END in *; lia | lia]. }
    pose proof (HOV 0%nat ltac:(lia)) as HB. rewrite Z.add_0_r in HB.
    unfold aview. rewrite HB. reflexivity. }
- (* q is a block: a0 = its address, no errno write *)
  destruct (QR HQ) as [Q1 Q2].
  eapply SRr_mono.
  { apply (m_blk W2 md2 regs2 mem2 (sp0 - 2144) (sptr_addr B ly2 q) (raZ regs) (s0Z regs) (bv_unsigned (getr regs 9))
      (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))
      (bv_unsigned (getr regs 2))).
    - exact SP2.
    - lia.
    - exact SPHI.
    - exact A02.
    - assert (RS : 0 <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia). lia.
    - exact RNG.
    - exact AFR.
    - exact IFR.
    - exact HRET. }
  intros W' c' _ POST. destruct POST as (EW & regs' & mem' & mat & Ec & MEQ & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G10 & GK).
  subst W' c'.
  exists regs', mem', (with_vm_backing (m_vm_lazy md2) mat md2).
  split. { unfold cfg_at. reflexivity. }
  split.
  { apply ap_mk_r. cs_cases.
    - rewrite G2. replace (sp0 - 2144 + 2144) with sp0 by lia. unfold sp0. rewrite w64_unsigned_r. reflexivity.
    - rewrite (GK 3%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 3 3%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact K3.
    - rewrite (GK 4%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 4 4%bv PRS ltac:(unfold acallee_saved; lia) eq_refl). exact K4.
    - rewrite G8. unfold s0Z. rewrite w64_unsigned_r. reflexivity.
    - rewrite G9, w64_unsigned_r. reflexivity.
    - rewrite G18, w64_unsigned_r. reflexivity.
    - rewrite G19, w64_unsigned_r. reflexivity.
    - rewrite G20, w64_unsigned_r. reflexivity.
    - rewrite G21, w64_unsigned_r. reflexivity.
    - rewrite (GK 22%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 22 22%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 22 ltac:(lia)).
    - rewrite (GK 23%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 23 23%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 23 ltac:(lia)).
    - rewrite (GK 24%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 24 24%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 24 ltac:(lia)).
    - rewrite (GK 25%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 25 25%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 25 ltac:(lia)).
    - rewrite (GK 26%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 26 26%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 26 ltac:(lia)).
    - rewrite (GK 27%bv ltac:(cbn; tauto)), (ap_get_r regsA regs2 27 27%bv PRS ltac:(unfold acallee_saved; lia) eq_refl).
      exact (KS 27 ltac:(lia)). }
  split; [exact G10|].
  split.
  { unfold ARXh_A. split; [exact Hinst|]. split; [|exact (proj2 (proj2 ARX2))].
    apply (ARCF' mem' mat);
    [intros x _ _; apply MEQ | intros a _ Hv; rewrite (aview_pw_r _ mem2 mem' a MEQ); exact Hv]. }
  split; [apply same_io_wvb_r|].
  split; [unfold RGtop.rkeep; split; [intros a _ _; apply aview_pw_r; exact MEQ | intros x _; exact (MEQ x)]|].
  split.
  { unfold RGtop.rwin, spZ. intros a Ha. fold sp0 in Ha. apply (apresent_pw_r _ mem2 mem' a MEQ). apply PW2. exact Ha. }
  split.
  { intros MN. apply (YAkMemnorm.memnorm_sub tfibsegs mem2 mem' MN). intros x b E. rewrite <- (MEQ x). exact E. }
  split. { intros _ i Hi. apply MEQ. }
  intros EQ. exfalso. exact (HQ EQ).
Qed.
End b.
End a.
