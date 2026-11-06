(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_x04.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* %04x's pcom arm (RT_pf_sh.v pcom_pcx_arm): a piece of fm's non-%s printf widening. Px04 is printf_common's
   flag '0', width '4', conversion 'x' (I_pcxgram.v pcx_dir / pcx_conv, PK_int) with one scalar argument: pa_of (AInt v)
   = PA_i v, which the walk does not range-check (ck_arg of PA_i is True), so its coverage entry is None (pc_cin1 Px04).
   Ported from the shared libc stdio proofs' proved proofs/omx-clap-core/fuzz_preset/lib/A/PSnpPcGram.v:
   pcx_pre's %04x step (:80-89; its Px04 coverage line :40), put in
   the per-piece form of RT_pf_sh.v's arms (pcom_pcx_arm_ps is the template). The I_pcxgram.v and FMsnprintfPf.v that
   both files read differ only in module paths (fuzz_preset -> fuzz_manifest, lib/A/PSnpBz -> lib/A/Bz,
   lib/Reusable/FMsnprintfPf -> lib/A/FMsnprintfPf). *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import I_pcxgram.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import FMpfStep RT_pf_sh.
Import ListNotations.
Open Scope Z_scope.

Lemma pcom_pcx_arm_Px04 : pcom_pcx_arm Px04.
Proof.
  intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
  injection H as <- <-. split.
  - intros n W. exists (1 + n)%nat. cbn [pf_code app map pcx_walk]. cbn. rewrite W. reflexivity.
  - cbn [pf_code pc_cin1 app map]. cbn. reflexivity.
Qed.
