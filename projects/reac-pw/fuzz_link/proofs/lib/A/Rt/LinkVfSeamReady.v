(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/FMgxaSeamReadyX.v, with its module paths changed; 124 of its 256 lines of code are new or changed and 626 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (fuzz_link.asan, pin 059dae63e07c): READINESS of the three interceptors (memcpy, memset,
   strnlen) for the GXA seam of musl vfprintf on link's memory FILE: LinkVfSeamGuard.seam_calls_ready_mf at link's
   three ready predicates (RT_gxa_calls_mem.copy_ready / set_ready, RT_gxa_strnlen.strn_ready), on the per-call
   normalized store FMgxaSeamNorm.cjnormv ly R.

   The memory-FILE twin of FMgxaSeamReady.v §5-6 (seam_ready_holds for the vsnprintf FILE). Sections 1-4 and the
   w_H8 part of §6 of that file do not depend on the FILE and are used as they are (the hull lemmas, the three
   *_intro lemmas, stack_rng_v, hull_of_pf_rng_H8, seam_dest_rng, cells_of_agree). What changes here:
   - the footprint is GXA's vf_mf_fp lo q f = [(lo, q); (f, f + 232); (f + 280, f + 1304)] (LinkVfMfA.v);
   - the runtime's cells at every store READY quantifies over (seam_cells_mf): an owned byte of the image's
     writable part lies outside the footprint because the stack window and the FILE block are high (the block by
     LinkVfSeamBlock.amf_block_high), where the vsnprintf seam used the FILE and the cookie on the stack above sp;
   - memcpy's destination is the buffer [f + 280, f + 1304) (the room arm of __fwritex, LinkMfSinkA.mf_out_ready),
     its source printf_core's stack or a range addressable in the store; vfprintf's 80-byte internal buffer is
     not used (buf_size = 1024), so its clauses go;
   - the buffer is carved out of R and its hull is visible, it lies below the stack window (f + 1304 <= lo), and
     its band bound 8 bytes past its end is the block's own (amem_range (f + 280) (1024 + 8)). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YG0q YI04 YA0n YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require Import RecAsanVfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMgxaSeamBase FMgxaSeamShadow.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.SetCall.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.StrnlenCall.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.LinkVfMfA.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memcpyw.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memsetw.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Spec.StrFun.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNormG.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNorm.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamReady.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_calls_mem.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_strnlen.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt.LinkVfSeamGuard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module GAF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Module GCC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.StrnlenCall.
Module GMF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.LinkVfMfA.
Module BR := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.R_m2s.
Module BMW := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memcpyw.
Module BSW := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memsetw.
Module BCW := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memchrw.
Module BNW := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_strnlenw.
Module NM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNorm.
Module NG := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNormG.
Module SR := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamReady.
Module FMM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_calls_mem.
Module RSN := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_strnlen.
Module LSG := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt.LinkVfSeamGuard.
Module BSF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Spec.StrFun.
Module CJF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Module GCA := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
(* strn_ready counts with the Bz tree's strnlen_res (RT_gxa_strnlen.v:100) *)
#[local] Abbreviation strnlen_res := BSF.strnlen_res.

#[local] Existing Instance N_img_asan_vf.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.

(* READY's store: a munch of cjnormv over the footprint keeps every owned byte of the image's writable part (the
   stack window and the FILE block are high). Those bytes are application memory, where cjnormv drops exactly what
   cjnorm drops (NM.seam_drop_app) *)
Lemma owned_agree_seam_mf : forall ly R S U (W : world tfibsegs) regs mem md (lo f : Z) (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo -> kHighMemBeg <= f ->
  CJF.munch (GMF.vf_mf_fp lo (spZ regs) f) (NM.cjnormv ly R (w_H W) mem) m' ->
  SR.owned_agree B ly S (mrestrict (w_H W) (unpoison U mem)) m'.
Proof.
intros ly R S U W regs mem md lo f m' HPRE Hlo Hf MU x Ho Hx.
pose proof HPRE as ((HAR & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
rewrite (MU x).
- unfold NM.cjnormv, NG.gdrop_normalize.
  rewrite (NM.seam_drop_app ly R x ltac:(unfold GAF.app_mem, GAF.LOWMEM_END; lia)).
  rewrite (NM.keep_of_writable x (NM.ro_addr_off x ltac:(lia)) ltac:(unfold TASK_SIZE; lia)).
  unfold cjstore, mrestrict. destruct (w_H W x); [reflexivity|].
  symmetry. exact (ARU_mem_low tfibsegs B ly S U W mem md x HU ltac:(unfold SHADOW_OFF; lia)).
- unfold GMF.vf_mf_fp. cbn [CJF.outside]. unfold kHighMemBeg in SK, Hf.
  split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma seam_cells_mf : forall ly R S U (W : world tfibsegs) regs mem md (lo f : Z) (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo -> kHighMemBeg <= f ->
  CJF.munch (GMF.vf_mf_fp lo (spZ regs) f) (NM.cjnormv ly R (w_H W) mem) m' ->
  BR.m2s_cells m' /\ BMW.icells m' /\ BSW.icells_ms m' /\ BNW.icells_sn m' /\ BCW.icells_mc m' /\ BNW.icells_sns m'.
Proof.
intros ly R S U W regs mem md lo f m' HPRE Hlo Hf MU.
pose proof HPRE as ((HAR & _) & _).
exact (SR.cells_of_agree B TB ly S (w_H W) (unpoison U mem) m' (proj1 HAR)
         (owned_agree_seam_mf ly R S U W regs mem md lo f m' HPRE Hlo Hf MU)).
Qed.

(* memcpy from ranges whose pf_rng and hull are known: the whole of copy_ready but the two ranges *)
Lemma seam_copy_of_rng_mf : forall ly R S U (W : world tfibsegs) regs mem md (lo f : Z) (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> kHighMemBeg <= f ->
  CJF.munch (GMF.vf_mf_fp lo (spZ regs) f) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= spZ regs - 368 -> 0 <= N ->
    (N = 0 \/ Dst + N <= sp - 64 - GCC.COPY_DEPTH \/ sp - 64 <= Dst) ->
    GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) Dst N -> (0 < N -> NM.sd_hull_kept ly R Dst N) ->
    (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) Dst N) ->
    GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N -> (0 < N -> NM.sd_hull_kept ly R P N) ->
    (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) P N) ->
    FMM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S U W regs mem md lo f m' HPRE Hlo HGEO Hf MU MK sp Dst P N H1 H2 HN SEP PD KD VD PP KP VP.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & _).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
destruct (seam_cells_mf ly R S U W regs mem md lo f m' HPRE Hlo Hf MU) as (C1 & C2 & _).
apply (SR.copy_ready_intro_loc m' (sp - 64) Dst P N N N).
- unfold BR.kHighShadowEnd, GCC.COPY_DEPTH. unfold GCA.OUT_DEPTH in H1. unfold kHighMemBeg in SK. lia.
- unfold kHighMemEnd in SK. lia.
- exact HN.
- unfold GCC.COPY_DEPTH in SEP |- *. lia.
- exact (GAF.pf_rng_kept _ _ Dst N PD MK).
- exact (GAF.pf_rng_kept _ _ P N PP MK).
- lia.
- lia.
- intros Hn0. exact (SR.hull_kept_v ly R (w_H W) mem m' Dst N MK (KD Hn0) Hn0 (SR.pf_rng_app _ Dst N PD) (VD Hn0)).
- intros Hn0. exact (SR.hull_kept_v ly R (w_H W) mem m' P N MK (KP Hn0) Hn0 (SR.pf_rng_app _ P N PP) (VP Hn0)).
- exact C1.
- exact C2.
Qed.

(* memset on printf_core's stack *)
Lemma seam_ready_set_mf : forall ly R S U (W : world tfibsegs) regs mem md (lo f : Z) (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md -> ly_stk_lo ly <= lo ->
  lo + GCA.OUT_DEPTH <= spZ regs - 368 -> kHighMemBeg <= f ->
  NM.sd_hull_kept ly R lo (spZ regs - lo) ->
  CJF.munch (GMF.vf_mf_fp lo (spZ regs) f) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst N, lo + GSC.SET_DEPTH <= sp -> sp <= Dst -> Dst + N + 8 <= spZ regs - 368 ->
    FMM.set_ready m' sp Dst N.
Proof.
intros ly R S U W regs mem md lo f m' HPRE Hlo HGEO Hf KW MU MK sp Dst N H1 H2 H3.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
unfold GCA.OUT_DEPTH, GSC.SET_DEPTH in *.
destruct (seam_cells_mf ly R S U W regs mem md lo f m' HPRE Hlo Hf MU) as (C1 & _ & C3 & _).
destruct (Z_le_gt_dec 0 N) as [HN|HN]; [|intros HN'; lia].
destruct (SR.stack_rng_v B LAWS ly R S U W mem md lo (spZ regs) Dst N HU KW Hlo ltac:(lia) HN ltac:(lia) ltac:(lia))
  as (PD & KD & VD).
apply (SR.set_ready_intro_cjnormv ly R (w_H W) mem m' sp Dst N N MK).
- unfold BR.kHighShadowEnd, GSC.SET_DEPTH. unfold kHighMemBeg in SK. lia.
- unfold kHighMemEnd in SK. lia.
- exact HN.
- right; right. exact H2.
- exact (proj1 (NM.pf_rng_cjnormv_back ly R (w_H W) mem Dst N PD)).
- exact (proj2 (NM.pf_rng_cjnormv_back ly R (w_H W) mem Dst N PD)).
- lia.
- exact KD.
- exact VD.
- exact C1.
- exact C3.
Qed.

(* memcpy into the buffer, from printf_core's stack or from a range addressable in the per-call store (its hull
   from w_H8, FMgxaSeamReady.hull_of_pf_rng_H8) *)
Lemma seam_ready_copy_mf : forall ly R S U (W : world tfibsegs) regs mem md (lo f : Z) (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 -> kHighMemBeg <= f -> f + 1304 <= lo ->
  NM.sd_hull_kept ly R lo (spZ regs - lo) -> NM.sd_hull_kept ly R (f + 280) 1024 ->
  GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) (f + 280) 1024 ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) (f + 280) 1024 ->
  CJF.munch (GMF.vf_mf_fp lo (spZ regs) f) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp Dst P N, lo + GCA.OUT_DEPTH <= sp -> sp <= spZ regs - 368 ->
    f + 280 <= Dst -> Dst + N <= f + 1304 -> 0 <= N ->
    (sp <= P /\ P + N + 8 <= spZ regs - 368 \/ GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N) ->
    FMM.copy_ready m' (sp - 64) Dst P N.
Proof.
intros ly R S U W regs mem md lo f m' HPRE HVR Hlo HGEO Hf HFlo KW KDD PDD VDD MU MK
  sp Dst P N H1 H2 HD1 HD2 HN HP.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
assert (PD : GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) Dst N).
{ replace Dst with (f + 280 + (Dst - (f + 280))) by lia.
  exact (GAF.pf_rng_sub _ (f + 280) 1024 (Dst - (f + 280)) N PDD ltac:(lia) HN ltac:(lia)). }
assert (KD : 0 < N -> NM.sd_hull_kept ly R Dst N)
  by (intros Hn0; exact (NM.sd_hull_kept_sub ly R (f + 280) 1024 Dst N KDD HD1 Hn0 ltac:(lia))).
assert (VD : 0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) Dst N)
  by (intros Hn0; exact (SR.hull_sub _ (f + 280) 1024 Dst N VDD HD1 Hn0 ltac:(lia))).
assert (PR : GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) P N /\ (0 < N -> NM.sd_hull_kept ly R P N) /\
             (0 < N -> shadow_hull_vis (aview tfibsegs (w_H W) mem) P N)).
{ destruct HP as [[HP1 HP2]|HP].
  - unfold GCA.OUT_DEPTH in *.
    exact (SR.stack_rng_v B LAWS ly R S U W mem md lo (spZ regs) P N HU KW Hlo ltac:(lia) HN ltac:(lia) ltac:(lia)).
  - split; [exact HP|]. split; [|exact (fun Hn0 => SR.hull_of_pf_rng_H8 B ly R S U W mem md P N HU HVR HP Hn0)].
    intros Hn0.
    exact (NM.hull_of_sh_kept ly R P N (proj2 (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N HP))
             Hn0 (SR.pf_rng_app _ P N (proj1 (NM.pf_rng_cjnormv_back ly R (w_H W) mem P N HP)))). }
destruct PR as (PP & KP & VP).
exact (seam_copy_of_rng_mf ly R S U W regs mem md lo f m' HPRE Hlo HGEO Hf MU MK sp Dst P N H1 H2 HN
         ltac:(right; left; unfold GCC.COPY_DEPTH, GCA.OUT_DEPTH in *; lia) PD KD VD PP KP VP).
Qed.

(* strnlen, with the hull of the bytes it checks from w_H8 *)
Lemma seam_ready_strn_mf : forall ly R S U (W : world tfibsegs) regs mem md (lo f : Z) (m' : word -> option byte),
  ecall_preU tfibsegs B ly S U W regs mem md ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 -> kHighMemBeg <= f ->
  CJF.munch (GMF.vf_mf_fp lo (spZ regs) f) (NM.cjnormv ly R (w_H W) mem) m' ->
  GAF.meta_kept (NM.cjnormv ly R (w_H W) mem) m' ->
  forall sp S0 N L buf, lo + GNC.STRN_DEPTH <= sp -> sp <= spZ regs - 368 ->
    GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) S0 L -> Z.min (strnlen_res N buf + 1) N <= L ->
    RSN.strn_ready m' sp S0 N buf.
Proof.
intros ly R S U W regs mem md lo f m' HPRE HVR Hlo HGEO Hf MU MK sp S0 N L buf H1 H2 PR HL.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & HUOK & HUP).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
destruct (seam_cells_mf ly R S U W regs mem md lo f m' HPRE Hlo Hf MU) as (C1 & _ & _ & C4 & C5 & C6).
destruct (NM.pf_rng_cjnormv_back ly R (w_H W) mem S0 L PR) as [PR0 KS].
apply (SR.strn_ready_intro_loc m' sp S0 N L buf); try assumption.
- unfold BR.kHighShadowEnd. unfold GNC.STRN_DEPTH in *. unfold kHighMemBeg in SK. lia.
- unfold kHighMemEnd in SK. lia.
- exact (GAF.pf_rng_kept _ _ S0 L PR MK).
- intros Hk.
  apply (SR.hull_kept_v ly R (w_H W) mem m' S0 _ MK
           (NM.sd_hull_kept_sub ly R S0 L S0 (Z.min (strnlen_res N buf + 1) N)
              (NM.hull_of_sh_kept ly R S0 L KS ltac:(lia) (SR.pf_rng_app _ S0 L PR0))
              ltac:(lia) ltac:(lia) ltac:(lia))
           Hk).
  + exact (GAF.app_ivl_sub S0 (S0 + L) S0 (S0 + Z.min (strnlen_res N buf + 1) N)
             (SR.pf_rng_app _ S0 L PR0) ltac:(lia) ltac:(lia)).
  + apply (SR.hull_prefix _ S0 L _ (SR.hull_of_pf_rng_H8 B ly R S U W mem md S0 L HU HVR PR ltac:(lia))). lia.
Qed.

(* READY of the memory-FILE seam at link's three predicates, for any carve-out list R that holds the buffer and the
   stack window and whose hulls the harness sees *)
Theorem seam_ready_holds_mf : forall ly R S U (W : world tfibsegs) regs mem md (lo f : Z),
  ecall_preU tfibsegs B ly S U W regs mem md ->
  In (f + 280, 1024) R -> In (lo, spZ regs - lo) R ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 ->
  kHighMemBeg <= f -> f + 1304 <= lo ->
  amem_range (f + 280) 1024 -> amem_range (f + 280) (1024 + 8) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (f + 280) 1024 ->
  LSG.seam_calls_ready_mf FMM.copy_ready FMM.set_ready RSN.strn_ready
    (NM.cjnormv ly R (w_H W) mem) (spZ regs) lo f.
Proof.
intros ly R S U W regs mem md lo f HPRE InD InW HVR Hlo HGEO Hf HFlo HAM HAM8 HRA.
pose proof HPRE as ((HAR & _ & _ & _ & HSPhi & _) & HUOK & HUP).
assert (SK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
assert (HV : shadow_hull_vis (aview tfibsegs (w_H W) mem) (f + 280) 1024)
  by exact (proj1 (Forall_forall _ _) HVR (f + 280, 1024) InD).
assert (KDD : NM.sd_hull_kept ly R (f + 280) 1024).
{ apply (NM.hull_kept_carved ly R (f + 280, 1024) InD); cbn [fst snd]; [unfold kHighMemBeg in Hf; lia|].
  exact (NM.amem_app (f + 280) 1024 ltac:(unfold kHighMemBeg in Hf; lia) HAM). }
assert (KW : NM.sd_hull_kept ly R lo (spZ regs - lo)).
{ apply (NM.hull_kept_carved ly R (lo, spZ regs - lo) InW); cbn [fst snd].
  - unfold kHighMemBeg in SK. lia.
  - unfold GAF.APPMEM_END. unfold kHighMemEnd in SK. lia. }
assert (PDD : GAF.pf_rng (NM.cjnormv ly R (w_H W) mem) (f + 280) 1024).
{ apply (NM.pf_rng_cjnormv ly R (w_H W) mem (f + 280) 1024 (NM.sh_kept_of_hull ly R (f + 280) 1024 KDD)).
  exact (SR.seam_dest_rng (w_H W) mem (f + 280) 1024%nat ltac:(unfold kHighMemBeg in Hf; lia) ltac:(cbn; lia)
           HAM HAM8 HRA). }
unfold LSG.seam_calls_ready_mf. intros m' MU _ MK.
split; [|split].
- intros sp Dst P N H1 H2 HD1 HD2 HN HP.
  exact (seam_ready_copy_mf ly R S U W regs mem md lo f m' HPRE HVR Hlo HGEO Hf HFlo KW KDD PDD HV MU MK
           sp Dst P N H1 H2 HD1 HD2 HN HP).
- exact (seam_ready_set_mf ly R S U W regs mem md lo f m' HPRE Hlo HGEO Hf KW MU MK).
- intros sp S0 N L buf H1 H2 PR HL.
  exact (seam_ready_strn_mf ly R S U W regs mem md lo f m' HPRE HVR Hlo HGEO Hf MU MK sp S0 N L buf H1 H2 PR HL).
Qed.

End C.
