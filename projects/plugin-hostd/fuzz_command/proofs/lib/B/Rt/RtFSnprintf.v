(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* fuzz_command.asan's snprintf on omx-clap-core/fuzz_manifest's GXA route, and the two route contracts the sprintf
   walk takes. fuzz_manifest's parametric route (relocated to this image by the address relocator:
   FMsnprintfFmI.fm_snprintf_gxaP, FMsnprintfSeamI.fm_seam_instP, RT_pf_shU.pcom_shzK, FMsnprintfSvfi / Svsn / Svsni)
   instantiated at fuzz_command's pieces pf_cmd_piece (all eight: literals %d %c %04x %02x %llu %s %.*s), every piece
   with its four arms (fuzz_manifest's arm files, as its own all-pieces instance FMsnprintfR1.v takes them), and
   carried to our statements:
   - FR_cmd (RtPFCmd.v) is inside FF_fmP pf_cmd_piece (FR_cmd_route): the same conjuncts, our local copies of
     pf_args_slack / pf_args_amem;
   - the read-only lists: omx-clap-core/fuzz_manifest's fm_cr and PCM_CR (the image's non-writable segments) compute
     to our CMD_SNP_CR / CMD_SP_CR;
   - snprintf (cmd_snprintf): the shared U form at 0x451d0 -> its AR form (sh_asnprintf_of_U) -> our text
     (RtPFCmd.cmd_asnprintf_of_sh, the owned read-only bytes from AR by RtPFCv.cmd_cr_consts_view);
   - printf_common at 0x48d28 (cmd_pcommon) and the vsnprintf interceptor at 0x498a4 (cmd_vsni): what RtFSprintf.v
     took as Section hypotheses APCOMMON and AVSNI.
   The world field w_H8 the seam uses (FMgxaSeamReady) is the class RtWH8.WH8 (Context in Section f), resolved in
   Section closed by its instance (the core's world field). No function is proved in this file: it instantiates. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require
RtPFH RtFormat RtAPI RtPFCv RtWH8 RtFSprintfFF RtFSprintfRun RtFSprintfW.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require FMgxaSeamDef FMgxaSeamPf FMgxaSeam RT_pf_sh RT_pf_shU FMsnprintfImg FMsnprintfFm FMsnprintfCr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require FMsnprintfMs32 FMsnprintfSvfi FMsnprintfSvsn FMsnprintfSvsni FMsnprintfSeamI FMsnprintfFmI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require FMpfArmPdSeam FMpfArmPcSeam FMpfArmPx04Seam FMgxaSeam02x FMpfArmPlluSeam RT_pf_d RT_pf_c RT_pf_x04 RT_pf_02x RT_pf_llu.
Import ListNotations.
Local Open Scope Z_scope.

Module SPf := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.FMgxaSeamPf.
Module RTS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.RT_pf_sh.

(* ---- the four arms of every piece (fuzz_manifest's FMsnprintfR1.v r1_*_arms, each piece its row's lemma) ---- *)
Lemma cmd_text_arms : forall p, pf_cmd_piece p -> SPf.seam_text_arm p.
Proof.
intros [b| | | | | | |] _.
- apply SPf.seam_text_arm_lit.
- exact FMpfArmPdSeam.seam_text_arm_pd.
- exact FMpfArmPcSeam.seam_text_arm_c.
- exact FMpfArmPx04Seam.seam_text_arm_x04.
- exact FMgxaSeam02x.seam_text_arm_px02.
- exact FMpfArmPlluSeam.seam_text_arm_pllu.
- exact SPf.seam_text_arm_ps.
- exact SPf.seam_text_arm_pps.
Qed.
Lemma cmd_pargs_arms : forall p, pf_cmd_piece p -> SPf.seam_pargs_arm p.
Proof.
intros [b| | | | | | |] _.
- apply SPf.seam_pargs_arm_lit.
- exact FMpfArmPdSeam.seam_pargs_arm_pd.
- exact FMpfArmPcSeam.seam_pargs_arm_c.
- exact FMpfArmPx04Seam.seam_pargs_arm_x04.
- exact FMgxaSeam02x.seam_pargs_arm_px02.
- exact FMpfArmPlluSeam.seam_pargs_arm_pllu.
- exact SPf.seam_pargs_arm_ps.
- exact SPf.seam_pargs_arm_pps.
Qed.
Lemma cmd_bytes_arms : forall p, pf_cmd_piece p -> SPf.seam_bytes_arm p.
Proof.
intros [b| | | | | | |] _.
- apply SPf.seam_bytes_arm_lit.
- exact FMpfArmPdSeam.seam_bytes_arm_pd.
- exact FMpfArmPcSeam.seam_bytes_arm_c.
- exact FMpfArmPx04Seam.seam_bytes_arm_x04.
- exact FMgxaSeam02x.seam_bytes_arm_px02.
- exact FMpfArmPlluSeam.seam_bytes_arm_pllu.
- exact SPf.seam_bytes_arm_ps.
- exact SPf.seam_bytes_arm_pps.
Qed.
Lemma cmd_pcx_arms : forall p, pf_cmd_piece p -> RTS.pcom_pcx_arm p.
Proof.
intros [b| | | | | | |] _.
- apply RTS.pcom_pcx_arm_lit.
- exact RT_pf_d.pcom_pcx_arm_Pd.
- exact RT_pf_c.pcom_pcx_arm_Pc.
- exact RT_pf_x04.pcom_pcx_arm_Px04.
- exact RT_pf_02x.pcom_pcx_arm_px02.
- exact RT_pf_llu.pcom_pcx_arm_llu.
- exact RTS.pcom_pcx_arm_ps.
- exact RTS.pcom_pcx_arm_pps.
Qed.

(* ---- FR_cmd is inside the route's family FF_fmP pf_cmd_piece ---- *)
Lemma cmd_slack_route : forall ws args, cmd_args_slack ws args -> FMgxaSeamDef.pf_args_slack ws args.
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
Lemma cmd_amem_route : forall ws args, cmd_args_amem ws args -> RTS.pf_args_amem ws args.
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
Lemma FR_cmd_route : forall rd rs f ws T, FR_cmd rd rs f ws T -> FMsnprintfFmI.FF_fmP pf_cmd_piece rd rs f ws T.
Proof.
intros rd rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham).
exists fmt, ps, args.
exact (conj Hf (conj Hp (conj Hk (conj Ha (conj Ht (conj Hq (conj Hlo (conj Hhi
  (conj (cmd_slack_route ws args Hsl) (conj Hne (cmd_amem_route ws args Ham))))))))))).
Qed.

(* ---- the read-only lists: omx-clap-core/fuzz_manifest's expression over the image's segments computes to ours ---- *)
Lemma cmd_fm_cr_snp : FMsnprintfCr.fm_cr = CMD_SNP_CR.
Proof. vm_compute. reflexivity. Qed.
Lemma cmd_fm_cr_sp : FMsnprintfCr.fm_cr = CMD_SP_CR.
Proof. vm_compute. reflexivity. Qed.
Lemma cmd_pcm_cr : RT_pf_shU.PCM_CR = CMD_SP_CR.
Proof. vm_compute. reflexivity. Qed.

(* ---- the bounds ---- *)
(* a closed comparison of two numerals (GXA's GLOBALS_TOP 0x606000 and VFA_DEPTH 5552 against ours) *)
Local Ltac zle := vm_compute; let Hc := fresh in intro Hc; discriminate Hc.
Lemma cmd_img_lo : CMD_IMG_LO <= 65536.
Proof. unfold CMD_IMG_LO. lia. Qed.
Lemma cmd_snp_window : FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= CMD_SNP_K.
Proof. rewrite FMsnprintfFm.fm_K_min_gxa. unfold CMD_SNP_K, ESTACK. lia. Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the shared snprintf text's family is a premise: a smaller family is served *)
Lemma snp_ff : forall segs B (FF1 FF2 : fmt_fam) K gc gv lo hi cr pc,
  (forall rd rs f ws T, FF2 rd rs f ws T -> FF1 rd rs f ws T) ->
  sh_asnprintf_realizesU segs B FF1 K gc gv lo hi cr pc -> sh_asnprintf_realizesU segs B FF2 K gc gv lo hi cr pc.
Proof.
intros segs B FF1 FF2 K gc gv lo hi cr pc HFF HU. unfold sh_asnprintf_realizesU in *.
intros ly S U W regs mem md d n f xs ws T cval. intros.
apply (HU ly S U W regs mem md d n f xs ws T cval); try assumption. apply HFF. assumption.
Qed.

Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.

(* printf_common at 0x48d28 (RtFSprintf.v's APCOMMON), for every window K >= 2320 *)
Lemma cmd_pcommon : forall K, 2320 <= K -> sh_apcommon_realizesUz tfibsegs B FR_cmd K CMD_SP_CR RtFSprintfRun.SP_PCOM.
Proof.
intros K HK.
apply (sh_apcommon_realizesUz_weaken tfibsegs B (RTS.FF_pcomK pf_cmd_piece) FR_cmd K RT_pf_shU.PCM_CR CMD_SP_CR
  RtFSprintfRun.SP_PCOM).
- intros rd rs f ws T H.
  exact (FMsnprintfFmI.FF_fmP_pcomK pf_cmd_piece pf_cmd_piece (fun p Hp => Hp) rd rs f ws T (FR_cmd_route rd rs f ws T H)).
- intros r1 Hr1. exists r1. rewrite <- cmd_pcm_cr. split; [exact Hr1 | lia].
- exact (RT_pf_shU.pcom_shzK B LAWS TB pf_cmd_piece cmd_pcx_arms K HK).
Qed.

Context {H8 : RtWH8.WH8}.

(* the seam at musl vfprintf at FR_cmd, at the window 5680 (>= GXA's VFA_DEPTH 5552) *)
Lemma cmd_seam : sh_avfprintf_icpt_realizesUx tfibsegs B FR_cmd 5680 RtPFH.FM_GOT_canary RtPFH.FM_canary CMD_IMG_LO
  CMD_IMG_HI FMsnprintfCr.fm_cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP.
Proof.
apply (sh_avfprintf_icpt_realizesUx_ff tfibsegs B (FMgxaSeamDef.pf_family_ro pf_cmd_piece 0x10000 0xa6bf8) FR_cmd 5680
  RtPFH.FM_GOT_canary RtPFH.FM_canary CMD_IMG_LO CMD_IMG_HI FMsnprintfCr.fm_cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP
  (fun rd rs f ws T H => FMsnprintfFmI.FF_fmP_ro pf_cmd_piece rd rs f ws T (FR_cmd_route rd rs f ws T H))).
exact (@FMsnprintfSeamI.fm_seam_instP _ _ B LAWS TB _ pf_cmd_piece cmd_text_arms cmd_pargs_arms cmd_bytes_arms 5680
  CMD_IMG_LO CMD_IMG_HI FMsnprintfCr.fm_cr ltac:(zle) cmd_img_lo ltac:(zle) FMsnprintfCr.fm_cr_ro_covered).
Qed.

(* the vsnprintf interceptor at 0x498a4 (RtFSprintf.v's AVSNI) with the window 2 * ESTACK: fuzz_manifest's composition
   (FMsnprintfFm.fm_snprintf_shared, the three asserts) at the seam's window Kv = 2 * ESTACK - 0x9d0 = 5680 *)
Lemma cmd_vsni : sh_avsnprintf_icpt_realizesUa tfibsegs B FR_cmd RtFSprintfW.SP_KVS CMD_GOTW CMD_GUARD
  CMD_IMG_LO CMD_IMG_HI CMD_SP_CR RtFSprintfRun.SP_VSNI.
Proof.
rewrite <- cmd_fm_cr_sp.
pose proof cmd_seam as SEAM.
pose proof (cmd_pcommon ESTACK ltac:(unfold ESTACK; lia)) as APC. rewrite <- cmd_fm_cr_sp in APC.
pose proof (FMsnprintfMs32.memset_icpt_realizesU B LAWS TB) as AMS.
pose proof RtFSprintfFF.FR_cmd_stable64 as STAB. pose proof RtFSprintfFF.FR_cmd_mono as MONO.
set (gc := RtPFH.FM_GOT_canary) in *. set (gv := RtPFH.FM_canary) in *.
assert (VFI : sh_avfprintf_icpt_realizesUx tfibsegs B FR_cmd (0x30 + 5680) gc gv CMD_IMG_LO CMD_IMG_HI
  FMsnprintfCr.fm_cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFPI).
{ apply (FMsnprintfSvfi.svfi_ok B LAWS TB FR_cmd gc gv CMD_IMG_LO CMD_IMG_HI FMsnprintfCr.fm_cr ESTACK 5680 (0x30 + 5680));
    first [assumption | unfold ESTACK; lia]. }
assert (VSN : sh_avsnprintf_realizesUa tfibsegs B FR_cmd (0x160 + 5680) gc gv CMD_IMG_LO CMD_IMG_HI
  FMsnprintfCr.fm_cr FMsnprintfImg.A_VSN).
{ apply (FMsnprintfSvsn.svsn_ok B LAWS FR_cmd STAB MONO (0x160 + 5680) (0x30 + 5680) gc gv CMD_IMG_LO CMD_IMG_HI
    FMsnprintfCr.fm_cr); first [assumption | reflexivity | unfold ESTACK; lia]. }
exact (FMsnprintfSvsni.svsni_ok B LAWS TB FR_cmd STAB MONO gc gv CMD_IMG_LO CMD_IMG_HI FMsnprintfCr.fm_cr
  RtFSprintfW.SP_KVS (0x160 + 5680) ESTACK
  ltac:(unfold RtFSprintfW.SP_KVS, ESTACK; lia) ltac:(unfold RtFSprintfW.SP_KVS, ESTACK; lia)
  ltac:(unfold RtFSprintfW.SP_KVS, ESTACK; lia) ltac:(unfold ESTACK; lia) APC VSN).
Qed.

(* snprintf at 0x451d0 on the shared U form at FR_cmd *)
Theorem cmd_snprintf_shU : sh_asnprintf_realizesU tfibsegs B FR_cmd CMD_SNP_K CMD_GOTW CMD_GUARD CMD_IMG_LO CMD_IMG_HI
  CMD_SNP_CR CMD_SNPRINTF_PC.
Proof.
rewrite <- cmd_fm_cr_snp.
apply (snp_ff tfibsegs B (FMsnprintfFmI.FF_fmP pf_cmd_piece) FR_cmd CMD_SNP_K CMD_GOTW CMD_GUARD CMD_IMG_LO CMD_IMG_HI
  FMsnprintfCr.fm_cr CMD_SNPRINTF_PC FR_cmd_route).
exact (FMsnprintfFmI.fm_snprintf_gxaP B LAWS TB pf_cmd_piece cmd_text_arms cmd_pargs_arms cmd_bytes_arms cmd_pcx_arms
  CMD_IMG_LO CMD_IMG_HI CMD_SNP_K cmd_img_lo ltac:(zle) cmd_snp_window).
Qed.

(* our snprintf contract (RtFormat.asnprintf_realizes) at the trampoline 0x451d0 *)
Theorem cmd_snprintf : RtFormat.asnprintf_realizes tfibsegs B RtAPI.PC_snprintf RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof.
unfold RtFormat.asnprintf_realizes, asnprintf_sh.
apply (cmd_asnprintf_of_sh tfibsegs B).
- intros ly S W regs mem md Hpre Hrom. exact (RtPFCv.cmd_cr_consts_view B TB ly S W regs mem md Hpre Hrom).
- apply sh_asnprintf_of_U. exact cmd_snprintf_shU.
Qed.
End f.

(* closed at the pinned record (AR_laws discharged as RtClosed.v does; WH8 by its instance) *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Theorem cmd_snprintf_closed : RtFormat.asnprintf_realizes tfibsegs B RtAPI.PC_snprintf RtAPI.A_SSP_GOT RtAPI.A_SSP_GUARD.
Proof. exact (cmd_snprintf B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
End closed.
