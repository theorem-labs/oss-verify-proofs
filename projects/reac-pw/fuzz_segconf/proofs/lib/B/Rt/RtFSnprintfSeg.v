(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtFSnprintfSeg.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* reac-pw/fuzz_segconf image B, interceptor interface rows 4 and 5: snprintf and the vsnprintf wrapper at segconf's
   format family RtPFSeg.FR_seg (lib/A/Rt/RtPFSeg.v), on omx-clap-core/fuzz_manifest's GXA route as this tree carries
   it relocated from plugin-hostd/fuzz_command (RtFSnprintf.v is the route at FR_cmd; this file is the same route at
   FR_seg):
   - FR_seg CMD_IMG_LO CMD_GOTW keeps under the route's memory changes (stable64, mono), lies inside the seam's family
     (SegGxaSeam.seg_family_ro) and inside printf_common's (SegPcomU.FF_pcomS);
   - printf_common at FR_seg: SegPcomU.pcom_shzS, weakened to the chain's read-only list;
   - the seam at musl vfprintf at FR_seg: SegGxaSeam.seg_seam_inst;
   - row 4: the shared U form at the snprintf trampoline by FMsnprintfFm.fm_snprintf_shared, then its AR form
     (sh_asnprintf_of_U) and our text (RtPFCmd.cmd_asnprintf_of_sh with RtPFCv.cmd_cr_consts_view): seg_snprintf;
   - the released snprintf text RtFormat.asnprintf_realizes at the same entry, because FR_cmd is FR_seg's special
     case at RtPFCmd's constants (seg_rtformat; RtPFSeg.v seg_pk takes every piece for this);
   - row 5: the vsnprintf interceptor at FR_seg (FMsnprintfSvsni.svsni_ok over musl vsnprintf, the vfprintf
     interceptor and the seam, as RtFSnprintf.cmd_vsni), carried to the trampoline (SegVsnTramp.vsni_tramp) and to
     the row's text (seg_avsnprintf_of_Ua: U = [], rt_rom_view -> consts_view): seg_vsnprintf.
   Closed at the pinned record in Section closed (AR_laws as RtClosed.v discharges it). No function is walked here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require
RtPFH RtFormat RtAPI RtPFCv RtWH8 RtDefs SegRtPC SegVsnTramp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require
FMgxaSeamDef FMgxaSeamFF FMgxaSeam RT_pf_sh RT_pf_shU FMsnprintfImg FMsnprintfFm FMsnprintfCr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require
FMsnprintfMs32 FMsnprintfSvfi FMsnprintfSvsn FMsnprintfSvsni.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require SegPfStep SegPcomU SegGxaSeam.
Import ListNotations.
Local Open Scope Z_scope.

Module FFF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.FMgxaSeamFF.
Module SPS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.SegPfStep.

(* ---- the image's numbers the route needs (RtFSnprintf.v:93-137, restated here so that this file Requires no
   sprintf file: segconf links no sprintf / vsprintf) ---- *)
Lemma seg_slack_route : forall ws args, cmd_args_slack ws args -> FMgxaSeamDef.pf_args_slack ws args.
Proof.
intros ws args. revert ws. induction args as [|a args IH]; intros ws H; [destruct ws; exact I|].
destruct a as [v|u|s]; destruct ws as [|w ws].
- exact (False_ind _ H).
- exact (IH ws H).
- exact (False_ind _ H).
- exact (IH ws H).
- exact (False_ind _ H).
- exact (conj (proj1 H) (IH ws (proj2 H))).
Qed.
Lemma seg_amem_route : forall ws args, cmd_args_amem ws args -> RT_pf_sh.pf_args_amem ws args.
Proof.
intros ws args. revert ws. induction args as [|a args IH]; intros ws H; [destruct ws; exact I|].
destruct a as [v|u|s]; destruct ws as [|w ws].
- exact I.
- exact (IH ws H).
- exact I.
- exact (IH ws H).
- exact I.
- exact (conj (proj1 H) (IH ws (proj2 H))).
Qed.
(* omx-clap-core/fuzz_manifest's read-only list over the image's segments computes to ours *)
Lemma seg_fm_cr_snp : FMsnprintfCr.fm_cr = CMD_SNP_CR.
Proof. vm_compute. reflexivity. Qed.
Lemma seg_img_lo : CMD_IMG_LO <= 65536.
Proof. unfold CMD_IMG_LO. lia. Qed.
Lemma seg_snp_window : FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= CMD_SNP_K.
Proof. rewrite FMsnprintfFm.fm_K_min_gxa. unfold CMD_SNP_K, ESTACK. lia. Qed.

(* ---- FR_seg against the route's families ---- *)
Lemma FR_seg_stable64 : forall lo hi, ff_stable64 (FR_seg lo hi).
Proof.
intros lo hi rd rd' rs f ws T (fmt & qs & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham) Hc.
destruct (FFF.fam_reads_stable64 rd rd' rs f fmt ws args Hc Hf Ha) as [Hf' Ha'].
exists fmt, qs, args.
exact (conj Hf' (conj Hp (conj Hk (conj Ha' (conj Ht (conj Hq (conj Hlo (conj Hhi (conj Hsl (conj Hne Ham)))))))))).
Qed.
Lemma FR_seg_mono : forall lo hi, ff_mono (FR_seg lo hi).
Proof.
intros lo hi rd rs rs' f ws T (fmt & qs & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham) Hs.
exists fmt, qs, args.
exact (conj (FFF.fmt_at_mono rd rs rs' f fmt Hf Hs) (conj Hp (conj Hk (conj (FFF.pf_args_asan_mono rd rs rs' ws args Ha Hs)
  (conj Ht (conj Hq (conj Hlo (conj Hhi (conj Hsl (conj Hne Ham)))))))))).
Qed.
(* inside the seam's family *)
Lemma FR_seg_ro : forall lo hi rd rs f ws T, FR_seg lo hi rd rs f ws T -> SegGxaSeam.seg_family_ro lo hi rd rs f ws T.
Proof.
intros lo hi rd rs f ws T (fmt & qs & args & Hf & Hp & _ & Ha & Ht & Hq & Hlo & Hhi & Hsl & _ & _).
exists fmt, qs, args.
exact (conj Hf (conj Hp (conj Ha (conj Ht (conj Hq (conj Hlo (conj Hhi (seg_slack_route ws args Hsl)))))))).
Qed.
(* inside printf_common's family, when the formats end below the image top *)
Lemma FR_seg_pcom : forall lo hi, hi <= TFIB_IMG_END ->
  forall rd rs f ws T, FR_seg lo hi rd rs f ws T -> SegPcomU.FF_pcomS rd rs f ws T.
Proof.
intros lo hi Hh rd rs f ws T (fmt & qs & args & Hf & Hp & _ & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham).
exists fmt, qs, args.
refine (conj Hf (conj Hne (conj _ (conj Hp (conj Ha (conj (seg_amem_route ws args Ham) (conj Ht Hq))))))).
lia.
Qed.
Lemma seg_gotw_img : CMD_GOTW <= TFIB_IMG_END.
Proof. vm_compute. discriminate. Qed.

(* FR_cmd is FR_seg's special case at RtPFCmd's constants *)
Lemma FR_cmd_seg : forall rd rs f ws T, FR_cmd rd rs f ws T -> FR_seg CMD_IMG_LO CMD_GOTW rd rs f ws T.
Proof.
intros rd rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham).
exists fmt, (map PRel ps), args.
split; [exact Hf|]. split; [exact (SPS.seg_parse_PRel fmt ps Hp)|].
split; [apply Forall_forall; intros x _; destruct x; exact I|].
split; [exact Ha|]. split; [rewrite SPS.seg_text_PRel; exact Ht|].
split; [apply SPS.seg_prec_pos_PRel; exact Hq|].
exact (conj Hlo (conj Hhi (conj Hsl (conj Hne Ham)))).
Qed.

(* a closed comparison of two numerals *)
Local Ltac zle := vm_compute; let Hc := fresh in intro Hc; discriminate Hc.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a contract is antitone in its family: the family is only a premise *)
Lemma cmd_asnprintf_ff_anti : forall segs B (FF1 FF2 : fmt_fam) K gc gv img_lo img_hi cr pc,
  (forall rd rs f ws T, FF2 rd rs f ws T -> FF1 rd rs f ws T) ->
  cmd_asnprintf_realizes segs B FF1 K gc gv img_lo img_hi cr pc ->
  cmd_asnprintf_realizes segs B FF2 K gc gv img_lo img_hi cr pc.
Proof.
intros segs B FF1 FF2 K gc gv img_lo img_hi cr pc Hsub H ly S W regs mem md d n f xs ws T cval
  P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 PF.
exact (H ly S W regs mem md d n f xs ws T cval P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 (Hsub _ _ _ _ _ PF)).
Qed.

(* the released GXA-route vsnprintf-interceptor form (svsni_ok proves it) gives row 5's text, given that rt_rom_view
   and the state give consts_view over cr (the form of RtPFCmd.cmd_asnprintf_of_sh) *)
Lemma seg_avsnprintf_of_Ua : forall segs B FF K gc gv img_lo img_hi cr pc,
  (forall ly S W regs mem md, ecall_pre segs B ly S W regs mem md -> RtDefs.rt_rom_view segs B W mem ->
    consts_view segs W mem cr) ->
  sh_avsnprintf_icpt_realizesUa segs B FF K gc gv img_lo img_hi cr pc ->
  seg_avsnprintf_icpt_realizes segs B FF K gc gv img_lo img_hi cr pc.
Proof.
intros segs B FF K gc gv img_lo img_hi cr pc DV HU ly S W regs mem md d n f ap ws T cval Hpre HK HW R10 R11 R12 R13
  Hrom.
intros.
eapply SRr_mono.
- apply (HU ly S [] W regs mem md d n f ap ws T cval); try eassumption;
    first [apply ecall_preU_nil; exact Hpre | exact (DV ly S W regs mem md Hpre Hrom)].
- intros W' c' _ (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HA & R). split; [reflexivity|].
  exists fx', regs', mem', md'.
  split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [apply ARU_nil in HA; exact HA | exact R].
Qed.

Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.
Context {H8 : RtWH8.WH8}.

(* printf_common at FR_seg, for every window K >= 2320, on the chain's read-only list *)
Lemma seg_pcommon : forall K, 2320 <= K ->
  sh_apcommon_realizesUz tfibsegs B (FR_seg CMD_IMG_LO CMD_GOTW) K FMsnprintfCr.fm_cr FMsnprintfImg.A_PCOM.
Proof.
intros K HK.
apply (sh_apcommon_realizesUz_weaken tfibsegs B SegPcomU.FF_pcomS (FR_seg CMD_IMG_LO CMD_GOTW) K RT_pf_shU.PCM_CR
  FMsnprintfCr.fm_cr FMsnprintfImg.A_PCOM).
- exact (FR_seg_pcom CMD_IMG_LO CMD_GOTW seg_gotw_img).
- intros r1 Hr1. exists r1. split; [exact Hr1 | lia].
- exact (SegPcomU.pcom_shzS B LAWS TB K HK).
Qed.

(* the seam at musl vfprintf at FR_seg, for every window K >= GXA's VFA_DEPTH *)
Lemma seg_seam : forall K, FMgxaSeam.GVA.VFA_DEPTH <= K ->
  sh_avfprintf_icpt_realizesUx tfibsegs B (FR_seg CMD_IMG_LO CMD_GOTW) K RtPFH.FM_GOT_canary RtPFH.FM_canary
    CMD_IMG_LO CMD_IMG_HI FMsnprintfCr.fm_cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP.
Proof.
intros K HK.
apply (sh_avfprintf_icpt_realizesUx_ff tfibsegs B (SegGxaSeam.seg_family_ro CMD_IMG_LO CMD_GOTW)
  (FR_seg CMD_IMG_LO CMD_GOTW) K RtPFH.FM_GOT_canary RtPFH.FM_canary CMD_IMG_LO CMD_IMG_HI FMsnprintfCr.fm_cr
  FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP (FR_seg_ro CMD_IMG_LO CMD_GOTW)).
exact (SegGxaSeam.seg_seam_inst B LAWS TB K CMD_IMG_LO CMD_IMG_HI FMsnprintfCr.fm_cr HK seg_img_lo ltac:(zle)
  FMsnprintfCr.fm_cr_ro_covered).
Qed.

(* ---- row 4 ---- *)
(* snprintf at the trampoline on the shared U form at FR_seg *)
Theorem seg_snprintf_shU : sh_asnprintf_realizesU tfibsegs B (FR_seg CMD_IMG_LO CMD_GOTW) CMD_SNP_K CMD_GOTW CMD_GUARD
  CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR CMD_SNPRINTF_PC.
Proof.
rewrite <- seg_fm_cr_snp.
assert (HV : FMgxaSeam.GVA.VFA_DEPTH = FMsnprintfFm.GXA_VF_DEPTH) by (rewrite FMgxaSeam.sa_vfa_depth; reflexivity).
apply (FMsnprintfFm.fm_snprintf_shared B LAWS TB (FR_seg CMD_IMG_LO CMD_GOTW) CMD_IMG_LO CMD_IMG_HI FMsnprintfCr.fm_cr
  2320 FMsnprintfFm.GXA_VF_DEPTH CMD_SNP_K (FR_seg_stable64 _ _) (FR_seg_mono _ _)).
- unfold ESTACK, FMsnprintfFm.GXA_VF_DEPTH. lia.
- unfold FMsnprintfFm.GXA_VF_DEPTH. lia.
- exact seg_snp_window.
- exact (seg_pcommon 2320 ltac:(lia)).
- exact (FMsnprintfMs32.memset_icpt_realizesU B LAWS TB).
- exact (seg_seam FMsnprintfFm.GXA_VF_DEPTH ltac:(rewrite HV; lia)).
Qed.

(* row 4 at the snprintf trampoline: RtPFSeg.seg_asnprintf_realizes *)
Theorem seg_snprintf : seg_asnprintf_realizes tfibsegs B CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR RtAPI.PC_snprintf
  RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof.
unfold seg_asnprintf_realizes.
apply (cmd_asnprintf_of_sh tfibsegs B).
- intros ly S W regs mem md Hpre Hrom. exact (RtPFCv.cmd_cr_consts_view B TB ly S W regs mem md Hpre Hrom).
- apply sh_asnprintf_of_U. exact seg_snprintf_shU.
Qed.

(* the released snprintf text at the same entry (RtAPI.rt_snprintf's field), from row 4 *)
Theorem seg_rtformat : RtFormat.asnprintf_realizes tfibsegs B RtAPI.PC_snprintf RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof.
unfold RtFormat.asnprintf_realizes, asnprintf_sh.
exact (cmd_asnprintf_ff_anti tfibsegs B _ _ _ _ _ _ _ _ _ FR_cmd_seg seg_snprintf).
Qed.

(* ---- row 5 ---- *)
(* the vsnprintf interceptor at FR_seg with the window 2 * ESTACK (RtFSnprintf.cmd_vsni at FR_seg) *)
Lemma seg_vsni : sh_avsnprintf_icpt_realizesUa tfibsegs B (FR_seg CMD_IMG_LO CMD_GOTW) SEG_VSN_K CMD_GOTW CMD_GUARD
  CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR FMsnprintfImg.A_VSNI.
Proof.
rewrite <- seg_fm_cr_snp.
pose proof (seg_seam 5680 ltac:(rewrite FMgxaSeam.sa_vfa_depth; lia)) as SEAM.
pose proof (seg_pcommon ESTACK ltac:(unfold ESTACK; lia)) as APC.
pose proof (FMsnprintfMs32.memset_icpt_realizesU B LAWS TB) as AMS.
pose proof (FR_seg_stable64 CMD_IMG_LO CMD_GOTW) as STAB. pose proof (FR_seg_mono CMD_IMG_LO CMD_GOTW) as MONO.
set (gc := RtPFH.FM_GOT_canary) in *. set (gv := RtPFH.FM_canary) in *.
assert (VFI : sh_avfprintf_icpt_realizesUx tfibsegs B (FR_seg CMD_IMG_LO CMD_GOTW) (0x30 + 5680) gc gv CMD_IMG_LO
  CMD_IMG_HI FMsnprintfCr.fm_cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFPI).
{ apply (FMsnprintfSvfi.svfi_ok B LAWS TB (FR_seg CMD_IMG_LO CMD_GOTW) gc gv CMD_IMG_LO CMD_IMG_HI
    FMsnprintfCr.fm_cr ESTACK 5680 (0x30 + 5680));
    first [assumption | unfold ESTACK; lia]. }
assert (VSN : sh_avsnprintf_realizesUa tfibsegs B (FR_seg CMD_IMG_LO CMD_GOTW) (0x160 + 5680) gc gv CMD_IMG_LO
  CMD_IMG_HI FMsnprintfCr.fm_cr FMsnprintfImg.A_VSN).
{ apply (FMsnprintfSvsn.svsn_ok B LAWS (FR_seg CMD_IMG_LO CMD_GOTW) STAB MONO (0x160 + 5680) (0x30 + 5680) gc gv
    CMD_IMG_LO CMD_IMG_HI FMsnprintfCr.fm_cr); first [assumption | reflexivity | unfold ESTACK; lia]. }
exact (FMsnprintfSvsni.svsni_ok B LAWS TB (FR_seg CMD_IMG_LO CMD_GOTW) STAB MONO gc gv CMD_IMG_LO CMD_IMG_HI
  FMsnprintfCr.fm_cr SEG_VSN_K (0x160 + 5680) ESTACK
  ltac:(unfold SEG_VSN_K, ESTACK; lia) ltac:(unfold SEG_VSN_K, ESTACK; lia)
  ltac:(unfold SEG_VSN_K, ESTACK; lia) ltac:(unfold ESTACK; lia) APC VSN).
Qed.

(* row 5 at the vsnprintf trampoline: RtPFSeg.seg_avsnprintf_realizes *)
Theorem seg_vsnprintf : seg_avsnprintf_realizes tfibsegs B CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR SegRtPC.PC_vsnprintf
  RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof.
unfold seg_avsnprintf_realizes.
apply seg_avsnprintf_of_Ua.
- intros ly S W regs mem md Hpre Hrom. exact (RtPFCv.cmd_cr_consts_view B TB ly S W regs mem md Hpre Hrom).
- apply (SegVsnTramp.vsni_tramp B LAWS). exact seg_vsni.
Qed.
End f.

(* ---- closed at the pinned record (AR_laws discharged as RtClosed.v does; WH8 by its instance) ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.
Theorem seg_snprintf_closed : seg_asnprintf_realizes tfibsegs B CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR RtAPI.PC_snprintf
  RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (seg_snprintf B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem seg_vsnprintf_closed : seg_avsnprintf_realizes tfibsegs B CMD_IMG_LO CMD_IMG_HI CMD_SNP_CR SegRtPC.PC_vsnprintf
  RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (seg_vsnprintf B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem seg_rtformat_closed : RtFormat.asnprintf_realizes tfibsegs B RtAPI.PC_snprintf RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (seg_rtformat B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
End closed.
