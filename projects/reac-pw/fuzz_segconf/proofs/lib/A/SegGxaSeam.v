(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/FMgxaSeamReadyX.v, with its module paths and module names changed; 317 of its 349 lines of code are new or changed and 726 lines of the source are left out. *)
(* THE GXA SEAM AT MUSL VFPRINTF FOR SEGCONF'S FORMATS: lib/A/FMgxaSeam.v fm_vfprintf_seamP over segconf's grammar
   (lib/A/Rt/RtPFSeg.v), closed as FMgxaSeamFm.v fm_vfprintf_seam_closedP and instantiated at this image's cells as
   FMsnprintfSeamI.v fm_seam_instP.
   - seg_family_ro is FMgxaSeamDef.v pf_family_ro over seg_parse / seg_text (no piece predicate: the model agreement
     SegGxaSeamPf.v covers every seg_piece);
   - seg_vfprintf_seam is fm_vfprintf_seamP's statement and proof, copied from this tree's relocated FMgxaSeam.v by
     records/interceptors/printf/tools/gen_seg_seam.py of the internal record commit 72eb1296d954 (sha256 89a3f2d6af8d), with the lines that name the released grammar
     replaced: the family's destructuring, the model agreement (SegGxaSeamPf.seg_model_agree), the model's argument
     list (SegPfText.seg_pargs) and its shape (seg_pargs_shape_pt), the text's bytes (seg_text_bytes) and the format's
     bytes (SegPfStep.seg_parse_bytes0). Every other line, every image numeral included, is the relocated file's;
   - seg_seam_inst discharges the three interceptor contracts and READY as FMgxaSeamFm.v does and instantiates at this
     image's cells with FMsnprintfSeamI.v's symbol lemmas. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFupoison RtPFPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import FMpfStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFShared RtPFSx RtPFCmd RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Mem Frame MState FP Cells Step Exec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_printf_core_common G_vfprintf_snf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require G_pad G_pop_arg G_fmt_fp_lib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA Require
AsanFacts SetCall StrnlenCall CopyCall G_printf_core_common G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import
RT_IImgA FMgxa_bridge FMgxaSeamBase FMgxaSeamPf FMgxaSeamDef FMgxaSeamShadow FMgxaSeamCall
FMgxaSeamPost FMgxaSeamCells FMgxaSeamFam FMgxaSeamGuard.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require FMgxaSeamNorm FMgxaSeamReady.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import FMgxaSeam.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require FMgxa_mem RT_gxa_strnlen FMsnprintfImg FMsnprintfSeamI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFH RtWH8.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import SegPfStep SegPfText SegGxaSeamPf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module RE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Regs6ss.
Module CJE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Exec.
Module CJC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Cells.
Module PRL := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec.Prelim.
Module GXC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GAF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA.AsanFacts.
Module GVA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GSA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA.G_printf_snfsink.
Module GCA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module NM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMgxaSeamNorm.
Module GCC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GXA.StrnlenCall.
Module SR := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMgxaSeamReady.
Module FMM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMgxa_mem.
Module RSN := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.RT_gxa_strnlen.
Module SEI := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.FMsnprintfSeamI.

#[local] Existing Instance A_img.

(* ---- the family the seam proves the contract for (FMgxaSeamDef.v pf_family_ro over seg_piece) ---- *)
Definition seg_family_ro (ilo ihi : Z) : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (qs : list seg_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ seg_parse fmt = Some qs /\ pf_args_asan rd rs ws args /\
    seg_text qs args = Some T /\ seg_prec_pos qs args /\
    ilo <= f /\ f + Z.of_nat (length fmt) + 1 <= ihi /\ pf_args_slack ws args.

Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis SYMS : AF0m.SegBSyms B.

(* the three interceptor call contracts, with their readiness predicates (FMgxaSeamCall.v) *)
Variable copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop.
Hypothesis SPEC_memcpy : @GCC.memcpy_stack_contract A_img copy_ready.
Hypothesis SPEC_memset : @GSC.memset_stack_contract A_img set_ready.
Hypothesis SPEC_strnlen : @GNC.strnlen_stack_contract A_img strn_ready.

(* READINESS at musl vfprintf's call: the stack window [lo, sp) below printf_core's depth, the FILE at
   Fp and the cookie at CK on the stack above sp and below 2^47, the destination [D, D + dn) writable,
   application memory with its band bound 8 bytes past its end (pf_rng's app_mem (D + i + 7),
   AsanFacts.v:80; those 8 bytes are asked nothing else), addressable, at or above 0, at most 2^40
   bytes and off the window, in a harness state that satisfies ecall_preU.
   The predicates must then meet FMgxaSeamGuard.v's seam_calls_ready on the per-call store GXA runs
   on, FMgxaSeamNorm.cjnormv ly R, for any carve-out list R that holds the destination (D, dn) and
   the stack window (lo, sp - lo) and whose hulls the harness sees.  The destination's own hull is
   that Forall at (D, dn), so READY does not state it twice. *)
Hypothesis READY : forall ly (R : list (Z * Z)) S U (W : world tfibsegs) regs mem md (lo Fp CK D : Z) (dn : nat),
  ecall_preU tfibsegs B ly S U W regs mem md ->
  In (D, Z.of_nat dn) R -> In (lo, spZ regs - lo) R ->
  Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r)) R ->
  ly_stk_lo ly <= lo -> lo + GCA.OUT_DEPTH <= spZ regs - 368 ->
  (forall a, lo <= a < spZ regs -> apresent (w_H W) mem a) ->
  spZ regs <= Fp -> Fp + 232 <= CK -> CK + 16 <= GAF.APPMEM_END ->
  dest_ok tfibsegs B ly S W regs mem Fp 232 -> dest_ok tfibsegs B ly S W regs mem CK 16 ->
  dest_ok tfibsegs B ly S W regs mem D (Z.of_nat dn) ->
  amem_range D (Z.of_nat dn) -> amem_range D (Z.of_nat dn + 8) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF D (Z.of_nat dn) ->
  0 <= D -> Z.of_nat dn <= 2 ^ 40 ->
  (D + Z.of_nat dn <= lo \/ spZ regs <= D) ->
  seam_calls_ready copy_ready set_ready strn_ready (NM.cjnormv ly R (w_H W) mem) (spZ regs) lo Fp CK D dn.

Theorem seg_vfprintf_seam :
  forall (K gc gv img_lo img_hi snw fam_lo fam_hi : Z) (cr : list (Z * Z)),
    GVA.VFA_DEPTH <= K -> gc = @sym A_img 0x22e18 -> gv = @sym A_img 0x34288 ->
    snw = @sym A_img GXC.K_SN_WRITE -> img_lo <= 65536 -> @GXC.GLOBALS_TOP A_img <= img_hi ->
    65536 <= fam_lo -> fam_hi <= @sym A_img 0x22e18 -> NM.ro_covered cr ->
    sh_avfprintf_icpt_realizesUx tfibsegs B
      (seg_family_ro fam_lo fam_hi) K gc gv img_lo img_hi cr snw (@sym A_img 0x7f000400).
Proof.
intros K gc gv img_lo img_hi snw fam_lo fam_hi cr HKd Egc Egv Esnw Hilo Hihi Hflo Hfhi HCOV.
unfold sh_avfprintf_icpt_realizesUx.
intros ly S U W regs mem md fp f ap bp cp s0 n0 ws T cval HPRE HK HWIN Ha0 Ha1 Ha2 HFILE Hbp HCK DFP DCK
  Hfp0 Hfp1 Hcp0 Hcp1 HCR HCRb HCRd Hgc Hgv Hgc0 Hgc1 Hgv0 Hgv1 Dgc Dgv HAP Hap0 Hap1 Dap HFAM
  Hn0 HT Hs0 Hs1 HPW DS0 AMS RAS SHV DIMG FRM0 HNUL FO1 FO2 FO3 DSL HTK HD8.
destruct HFAM as (fmtb & qs & args0 & HFA & HPS & HPA & HPT & HPP & HFLO & HFHI & HSL).
(* ---- the harness state ---- *)
pose proof HPRE as ((HAR & HRET & _ & _ & HSPhi & _ & _ & _) & HUOK & HUP).
assert (HARU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
assert (HSTK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
unfold kHighMemBeg, kHighMemEnd in HSTK. pose proof sa_vfa_depth as VFA.
pose proof sa_globals_top as GT. pose proof sa_globals_top_a as GTA.
pose proof sa_sym_got_ssp as S22. pose proof sa_sym_guard as S34.
rewrite GT in Hihi. rewrite S22 in Hfhi.
assert (Esp : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
(* ---- the written part: GXA's dn ---- *)
assert (SNL : sn_len n0 T = Z.min n0 (Z.of_nat (length T)) + 1) by (apply sa_sn_len_eq; lia).
remember (Z.to_nat (sn_len n0 T)) as dn eqn:Edn.
assert (HDN : Z.of_nat dn = sn_len n0 T) by (subst dn; rewrite Z2Nat.id; lia).
assert (DS0' : dest_ok tfibsegs B ly S W regs mem s0 (Z.of_nat dn)) by (rewrite HDN; exact DS0).
assert (AMS' : amem_range s0 (Z.of_nat dn)) by (rewrite HDN; exact AMS).
assert (AMS8 : amem_range s0 (Z.of_nat dn + 8)) by (rewrite HDN; exact HD8).
assert (RAS' : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF s0 (Z.of_nat dn))
  by (rewrite HDN; exact RAS).
assert (WD : forall a, s0 <= a < s0 + Z.of_nat dn -> writable_at tfibsegs (cjstore (w_H W) mem) a)
  by (intros a Ha; exact (proj1 (DS0' a Ha))).
destruct (rw_cells_block_hd0 (w_H W) mem s0 dn ltac:(lia) ltac:(lia) WD
            (fun a Ha => sa_writable_aview _ _ _ (WD a Ha)) HNUL ltac:(lia)) as (junkd & LJ & RD).
assert (DIMG' : s0 + Z.of_nat dn <= 65536 \/ 0x601000 <= s0).
{ rewrite HDN. unfold zdisjoint in DIMG. cbn [fst snd] in DIMG. lia. }
(* ---- the family: format, pieces, arguments, text ---- *)
pose proof HFA as (Hf0 & _ & _ & _ & HFRA & _).
(* the slot words are words, so the arguments fit (FMpfStep.v pf_arg_fit) *)
assert (HWR : Forall (fun w => 0 <= w < 2 ^ 64) ws).
{ apply Forall_forall. intros w Hin. apply (In_nth ws w 0) in Hin as (i & Hi & <-).
  exact (sa_rdword_range _ _ _ _ (HAP i Hi)). }
pose proof (sa_args_fit _ _ ws args0 HPA HWR) as HFIT.
assert (HU : forall u, In (AU64 u) args0 -> 0 <= u < 2 ^ 64).
{ intros u Hin. rewrite Forall_forall in HFIT. exact (HFIT _ Hin). }
assert (HTl : PRL.zlength T <= 2147483647) by (unfold PRL.zlength; lia).
(* GXA's model on the format, with the model's own argument list PA (the pieces' seam arms) *)
destruct (seg_model_agree fmtb qs args0 T HPS HPT HFIT HTl) as (AM & AP1 & _).
set (PA := seg_pargs qs args0) in AM.
pose proof (seg_pargs_shape_pt qs args0 T HPT) as HPAS. fold PA in HPAS.
assert (TB : Forall (fun c => 0 <= c < 256) T)
  by exact (seg_text_bytes qs args0 T (seg_parse_codes qs fmtb HPS) HFIT HPT).
assert (ZL : PRL.zlength (fmtb ++ [0]) = Z.of_nat (length fmtb) + 1).
{ unfold PRL.zlength. rewrite length_app. cbn [length]. lia. }
assert (ERS : vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp
              = [(spZ regs - K, spZ regs - (spZ regs - K)); (s0, Z.of_nat dn); (fp, 232); (cp, 16)]).
{ unfold vfp_out. rewrite HDN. replace (spZ regs - (spZ regs - K)) with K by lia. reflexivity. }
(* ---- the FILE, the cookie, the stack-protector cells ---- *)
assert (Hbp64 : bp < 2 ^ 64).
{ assert (L11 : (11 < length (sn_file snw bp cp))%nat) by (unfold sn_file; cbn; lia).
  pose proof (HFILE 11%nat L11) as X. unfold sn_file in X. cbn [nth] in X.
  pose proof (sa_rdword_range _ _ _ _ X). lia. }
(* GXA (4) with the frame order: the FILE, the cookie and the slots lie below TASK_SIZE *)
assert (HTB : fp + 232 <= TASK_SIZE /\ cp + 16 <= TASK_SIZE /\ ap + 8 * PRL.zlength (map w64 ws) <= TASK_SIZE).
{ unfold TASK_SIZE, PRL.zlength. rewrite length_map. lia. }
(* the read agreement the normalized store needs, from the contract's constants *)
pose proof (NM.ro_agree_of_consts W mem cr HCR HCOV) as HRO.
assert (WGC : forall a, gc <= a < gc + 8 -> writable_at tfibsegs (cjstore (w_H W) mem) a).
{ intros a Ha. apply sa_ssp_writable. left. rewrite Egc, S22 in Ha. lia. }
assert (WGV : forall a, gv <= a < gv + 8 -> writable_at tfibsegs (cjstore (w_H W) mem) a).
{ intros a Ha. apply sa_ssp_writable. right. rewrite Egv, S34 in Ha. lia. }
(* ---- the seam's carve-out list: what the per-call normalization keeps, and its visible hulls.
   The window's hull and the musl prefix's hull are AR's, not the contract's (FMgxaSeamReady.v
   stack_hull, prefix_hull); the rest are the contract's own ---- *)
pose proof HFA as (_ & _ & _ & AMF & _ & _).
destruct (NM.seam_drop_keeps ly (spZ regs - K) K s0 (Z.of_nat dn) f fmtb ws args0
            (aview tfibsegs (w_H W) mem) (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp)
            ltac:(lia) ltac:(lia) ltac:(lia) Hs0 AMS' Hf0 AMF HPA) as (KD & KF & KW & KP & KA & KAPP).
assert (HVR : Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r))
                (NM.seam_R s0 (Z.of_nat dn) f fmtb (spZ regs - K) K ws args0)).
{ apply (NM.seam_R_hulls (aview tfibsegs (w_H W) mem)
           (vfp_out K (spZ regs) s0 (sn_len n0 T) fp cp)).
  - rewrite HDN. exact SHV.
  - exact HFA.
  - eapply SR.stack_hull; try exact LAWS; try exact HARU; lia.
  - eapply SR.prefix_hull; try exact SYMS; try exact HARU.
  - exact HPA. }
assert (InD : In (s0, Z.of_nat dn) (NM.seam_R s0 (Z.of_nat dn) f fmtb (spZ regs - K) K ws args0))
  by (unfold NM.seam_R; apply in_eq).
assert (InW : In (spZ regs - K, spZ regs - (spZ regs - K))
                (NM.seam_R s0 (Z.of_nat dn) f fmtb (spZ regs - K) K ws args0)).
{ replace (spZ regs - (spZ regs - K)) with K by lia. unfold NM.seam_R. apply in_cons, in_cons, in_eq. }
set (RN := NM.seam_R s0 (Z.of_nat dn) f fmtb (spZ regs - K) K ws args0) in *.
(* ---- GXA's walk, at the harness's arguments ---- *)
assert (APF : GVA.args_pf (cjstore (w_H W) mem) (map w64 ws) PA)
  by exact (sa_args_pf_pt _ _ _ _ HPAS (args_pf_of_pf_args_asan (w_H W) mem _ ws args0 HPA HSL)).
pose proof (seam_vfprintf_a copy_ready set_ready strn_ready SPEC_memcpy SPEC_memset SPEC_strnlen) as G.
unfold GVA.vfprintf_snf_a_stmt in G.
specialize (G (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
  (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
  (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
  (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
  (getr regs 29) (getr regs 30) (getr regs 31) (@fp_regs fx) (@fp_csr fx) (NM.cjnormv ly RN (w_H W) mem)
  fp cp s0 n0 (PRL.zlength T) bp f ap dn junkd (fmtb ++ [0]) (map w64 ws) PA
  (spZ regs - K) (w64 cval) (PRL.zlength T) T).
cbv zeta in G. rewrite Esp in G.
eapply srr_of_gxa_evt.
{ exact AF0x.Hwx_tfa. }
{ eapply sa_evt_eqv.
  - eapply NM.evt_from_norm_MS_v; [exact HRO|]. apply G; clear G.
    + exact Ha0.
    + exact Ha1.
    + exact Ha2.
    + apply NM.file_cjnormv;
        [lia | lia | apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END, TASK_SIZE in *; lia |].
      exact (rw_cells_snf_file (w_H W) mem fp snw bp cp Esnw Hfp0 ltac:(lia) HFILE (fun a Ha => proj1 (DFP a Ha))).
    + apply NM.cookie_cjnormv;
        [lia | lia | apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END, TASK_SIZE in *; lia |].
      exact (rw_cells_pair (w_H W) mem cp s0 n0 Hcp0 ltac:(lia) HCK (fun a Ha => proj1 (DCK a Ha))).
    + apply NM.dest_cjnormv; [lia | unfold TASK_SIZE, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia
                             | lia
                             | intros a Ha;
                               exact (app_mem_of_amem_range s0 (Z.of_nat dn) a AMS' ltac:(lia) ltac:(lia) ltac:(lia))
                             | exact RD].
    + exact LJ.
    + apply NM.fmt_cjnormv; [exact HRO | rewrite ZL; lia |].
      exact (fmt_bytes_of_fmt_at (w_H W) mem _ f fmtb HFA ltac:(lia)).
    + exact (seg_parse_bytes0 fmtb qs HPS).
    + exact AP1.
    + apply NM.va_area_cjnormv;
        [exact HRO | lia
        | apply GAF.high_stack_app;
          [unfold GAF.HIGHMEM_BEG; lia | unfold GAF.APPMEM_END, PRL.zlength; rewrite length_map; lia] |].
      exact (va_area_of_words_at (w_H W) mem ap ws Hap0 ltac:(lia) HAP).
    + apply NM.args_ok_cjnormv;
        [exact HRO | exact (NM.args_task_of_pf _ _ _ APF) | exact (NM.args_app_of_pf _ _ _ APF) |].
      apply (sa_args_ok_pt _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPAS).
      exact (args_ok_of_pf_args_asan (w_H W) mem _ ws args0 fp (spZ regs - K) 0 cp 16 s0 (Z.of_nat dn)
               (spZ regs - K) (spZ regs) (spZ regs - K) HPA HSL HU ERS eq_refl eq_refl eq_refl ltac:(lia)).
    + exact AM.
    + lia.
    + unfold PRL.zlength. lia.
    + rewrite HDN, SNL. unfold PRL.zlength. lia.
    + lia.
    + apply NM.stk_window_cjnormv;
        [lia | unfold TASK_SIZE; lia | apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia |].
      exact (stk_of_apresent (w_H W) mem (spZ regs - K) (spZ regs) ltac:(lia) ltac:(lia) HWIN).
    + lia.
    + lia.
    + lia.
    + apply NM.ssp_cells_cjnormv.
      exact (ssp_cells_of_view (w_H W) mem gc gv cval (w64 cval) Egc Egv Hgc Hgv eq_refl WGC WGV).
    + exact (NM.mem_inv_cjnormv ly RN (w_H W) mem).
    + exact FRM0.
    + rewrite ZL. lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold PRL.zlength. rewrite length_map. lia.
    + lia.
    + unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMS'. lia.
    + unfold PRL.zlength. rewrite length_map. lia.
    + lia.
    + assert (VR : GVA.vf_ready_a (GSA.snf_out_ready copy_ready) set_ready strn_ready copy_ready SEAM_INV
                     (NM.cjnormv ly RN (w_H W) mem) (spZ regs) (spZ regs - K) fp cp s0 dn n0 bp f ap
                     (fmtb ++ [0]) (map w64 ws) PA).
      { apply NM.vf_ready_cjnormv.
        * rewrite ZL. lia.
        * rewrite ZL. apply pf_rng_of_view; [lia | lia | lia | | exact HFRA].
          unfold amem_range, kLowMemEnd. left. lia.
        * rewrite ZL. exact (NM.sh_kept_of_hull ly RN f (Z.of_nat (length fmtb) + 1) KF).
        * exact (musl_prefix_of_ARU B ly S U W mem md (zsh_rodata_of_tfib B SYMS) HARU).
        * exact (NM.sh_kept_of_hull ly RN (@sym A_img 0x1029e) 9 KP).
        * exact APF.
        * exact (sa_args_kept_pt _ _ _ _ _ HPAS KA).
        * apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia.
        * apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END, TASK_SIZE in *; lia.
        * apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END, TASK_SIZE in *; lia.
        * intros a Ha. exact (app_mem_of_amem_range s0 (Z.of_nat dn) a AMS' ltac:(lia) ltac:(lia) ltac:(lia)).
        * unfold GCA.OUT_DEPTH. lia.
        * exact (READY ly RN S U W regs mem md (spZ regs - K) fp cp s0 dn HPRE InD InW HVR ltac:(lia)
                   ltac:(unfold GCA.OUT_DEPTH; lia) HWIN FO1 FO2 ltac:(unfold GAF.APPMEM_END, TASK_SIZE in *; lia)
                   DFP DCK DS0' AMS' AMS8 RAS' ltac:(lia) ltac:(lia) ltac:(lia)). }
      exact (proj2 VR).
  - split; [apply RE.xregs_eqv_sym, RE.mkR_eqv_of; reflexivity|]. repeat split. }
(* ---- GXA's post, read as the harness's ---- *)
intros ms' model' (y & (st0 & HQ & HREL & HSAME) & HEQ) HSBM _.
pose proof (NM.post_from_norm_a_v SEAM_INV ly RN (w_H W) mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              HRO HREL HSAME HQ) as HP.
clear HQ.
destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & fjunk & m'
                & Ey & MU & WM & FRM' & FREG & STK' & SSP' & DST' & CKC' & FPC').
subst y. rewrite Esp in MU.
destruct ms' as [R' F' pc' svc' rv' fc'' mm ro'].
destruct HEQ as (HR & HF & HPC & HSVC & HRV & HFC & HM & HROM).
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom CJMS.MS] in HR, HF, HPC, HSVC, HRV, HFC, HM, HROM.
subst F' pc' svc' rv' fc'' mm ro'.
assert (EPC : CJMS.ret_pc (getr regs 1) = w64 (raZ regs)) by exact (ret_pc_raZ _ HRET).
assert (OWN : forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a ->
          CJF.outside [(spZ regs - K, spZ regs); (fp, fp + 232); (cp, cp + 16); (s0, s0 + Z.of_nat dn)] a).
{ apply (win_owned B LAWS ly S U W regs mem md _ HPRE). intros a Ha HE.
  apply Exists_cons in HE; destruct HE as [HE|HE]; [cbn [fst snd] in HE; left; lia|].
  apply Exists_cons in HE; destruct HE as [HE|HE];
    [cbn [fst snd] in HE; right; exact (proj1 (proj2 (DFP a ltac:(lia))))|].
  apply Exists_cons in HE; destruct HE as [HE|HE];
    [cbn [fst snd] in HE; right; exact (proj1 (proj2 (DCK a ltac:(lia))))|].
  apply Exists_cons in HE; destruct HE as [HE|HE];
    [cbn [fst snd] in HE; right; exact (proj1 (proj2 (DS0' a ltac:(lia))))|].
  inversion HE. }
cbv beta. split; [reflexivity|].
exists (YK11.mkFP Ft fc'), R', (munrestrict (w_H W) mem m'), model'.
split.
{ rewrite cfg_of_ms. unfold unrestrict.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite EPC. reflexivity. }
split.
{ intros k Hk. exact (FREG k Hk). }
split; [exact FRM'|].
split.
{ destruct (aru_of_window B LAWS ly S U W regs mem md m' _ HPRE MU WM OWN) as (md2 & SB2 & ARU2).
  pose proof (same_but_materialized_frame md md2 SB2) as (_ & Hv2 & Hl2 & _).
  pose proof (same_but_materialized_frame md model' HSBM) as (_ & Hv' & Hl' & _).
  exact (sa_ARU_model_same B ly S U W _ md2 model' ARU2 ltac:(congruence) ltac:(congruence)). }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct RR as [RR|RR];
    [subst r; rewrite !sa_getr_nz by reflexivity; rewrite <- (HR _) by reflexivity; reflexivity|]).
  subst r; rewrite !sa_getr_nz by reflexivity; rewrite <- (HR _) by reflexivity; reflexivity. }
split; [exact HSBM|].
split.
{ rewrite sa_getr_nz by reflexivity. rewrite <- (HR _) by reflexivity. reflexivity. }
split.
{ intros i Hi.
  destruct DST' as [[CW BA] _].
  cbn [CJC.cells_wf CJC.cell_wf CJC.cells_bytes CJC.cbytes] in CW, BA.
  rewrite app_nil_r in BA. destruct CW as [CWL _].
  match type of BA with CJM.bytes_at _ _ _ ?bs0 => set (bs := bs0) in BA, CWL end.
  assert (HV : forall a, s0 <= a < s0 + Z.of_nat (length bs) -> w_H W (Z_to_bv 64 a) = false).
  { intros a Ha. rewrite CWL in Ha. exact (sa_writable_vis W mem a (WD a Ha)). }
  pose proof (view_of_bytes_at (w_H W) mem m' s0 bs BA HV (Z.to_nat i) ltac:(rewrite CWL; lia)) as V.
  rewrite Z2Nat.id in V by lia. rewrite V. f_equal.
  unfold bs. rewrite sa_nth_zb_app by (rewrite length_firstn; lia).
  unfold sn_bytes. apply sa_bv_u8. apply sa_nth_range. apply Forall_app. split.
  - apply sa_Forall_firstn. exact TB.
  - constructor; [lia | constructor]. }
split.
{ intros a Ha Hd HN.
  apply (win_view_out (w_H W) mem m' _ MU a Ha). cbn [CJF.outside].
  assert (N1 : ~ (spZ regs - K <= a < spZ regs - K + K)) by (intros X; apply HN; apply Exists_cons_hd; exact X).
  assert (N2 : ~ (fp <= a < fp + 232)) by (intros X; apply HN; apply Exists_cons_tl; apply Exists_cons_hd; exact X).
  assert (N3 : ~ (cp <= a < cp + 16))
    by (intros X; apply HN; apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd; exact X).
  rewrite HDN. repeat split; lia. }
apply (win_present_off (w_H W) mem m' _ MU WM).
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed.

End S.

(* ---- closed and at this image's cells (FMgxaSeamFm.v fm_vfprintf_seam_closedP, FMsnprintfSeamI.v fm_seam_instP) ---- *)
Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : AF0m.SegBSyms B.
Context {H8 : RtWH8.WH8}.

(* the family's range: the image's first byte to the GOT word musl vfprintf loads its guard pointer from *)
Theorem seg_seam_inst : forall K img_lo img_hi cr,
  GVA.VFA_DEPTH <= K -> img_lo <= 65536 -> @GXC.GLOBALS_TOP A_img <= img_hi -> NM.ro_covered cr ->
  sh_avfprintf_icpt_realizesUx tfibsegs B (seg_family_ro CMD_IMG_LO CMD_GOTW) K
    RtPFH.FM_GOT_canary RtPFH.FM_canary img_lo img_hi cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP.
Proof.
intros K img_lo img_hi cr HK Hlo Hhi HCOV.
rewrite SEI.si_vfp.
exact (seg_vfprintf_seam B LAWS TB FMM.copy_ready FMM.set_ready RSN.strn_ready
  FMM.memcpy_stack_contract_A FMM.memset_stack_contract_A RSN.strnlen_stack_contract_A
  (SR.seam_ready_holds B LAWS TB)
  K _ _ img_lo img_hi _ CMD_IMG_LO CMD_GOTW cr HK SEI.si_got SEI.si_guard SEI.si_snw Hlo Hhi
  SEI.si_fam_lo SEI.si_fam_hi HCOV).
Qed.
End F.
