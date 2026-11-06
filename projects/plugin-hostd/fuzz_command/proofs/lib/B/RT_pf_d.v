(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_d.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* The conversion %d (Pd) in ASan printf_common's scan, a piece of fm's non-%s printf widening, as the per-piece
   pcom arm (RT_pf_sh.v pcom_pcx_arm). The consumers take it as
   `forall p, PK p -> pcom_pcx_arm p`: RT_pf_sh.v pcx_K / pcomx_K, RT_pf_shU.v pcom_shzK, FMsnprintfFmI.v fm_snprintf_gxaP.
   %d is printf_common's grammar step pcx_dir (100 :: rest) = Some (false, PP_none, PK_int, rest) (I_pcxgram.v): no flag,
   width, precision or length modifier, an int conversion, so the walk consumes one argument word, pa_of (AInt v) = PA_i v,
   which pcx_fits accepts for PK_int, and gives it the coverage entry None (pc_cin1 Pd = [None]; ck_arg of PA_i is True).
   The seam arms of Pd are fm's lib/A/FMpfArmPdSeam.v (seam_text_arm_pd / seam_pargs_arm_pd / seam_bytes_arm_pd,
   with the seam-side control seam_pd_control); the printf_common-side control is lib/A/FMpfArmPdCtl.v.
   New file; nothing else is edited. *)
(* Modified by Theorem Labs, 2026-10: the proof is RT_pf_sh.v pcom_pcx_arm_ps (6c733891261 :141-147) with the step at
   %d in place of %s, the %d step as in the shared libc stdio proofs'
   proofs/omx-clap-core/fuzz_preset/lib/A/PSnpPcGram.v (its %c case) and
   proofs/libreac/fuzz_disco/lib/A/Prog/pf_bridge.v pcx_cargs_ok (its Pd case). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import I_pcxgram.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFPf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import FMpfStep RT_pf_sh.
Import ListNotations.
Open Scope Z_scope.

Lemma pcom_pcx_arm_Pd : pcom_pcx_arm Pd.
Proof.
  intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
  injection H as <- <-. split.
  - intros n W. exists (1 + n)%nat. cbn [pf_code app map pcx_walk]. cbn. rewrite W. reflexivity.
  - cbn [pf_code pc_cin1 app map]. cbn. reflexivity.
Qed.
