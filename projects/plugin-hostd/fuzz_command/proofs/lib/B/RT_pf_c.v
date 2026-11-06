(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_c.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* %c's pcom arm (RT_pf_sh.v pcom_pcx_arm): a piece of fm's non-%s printf widening. Pc is printf_common's conversion
   'c' (I_pcxgram.v pcx_dir / pcx_conv, PK_char) with one scalar argument: pa_of (AInt v) = PA_i v, which the walk does
   not range-check (ck_arg of PA_i is True), so its coverage entry is None (pc_cin1 Pc).
   Ported from the shared libc stdio proofs' proved proofs/omx-clap-core/fuzz_preset/lib/A/PSnpPcGram.v:
   pcx_pre's %c step (:58-67; its Pc coverage line :39), put in the
   per-piece form of RT_pf_sh.v's arms (pcom_pcx_arm_ps is the template). The I_pcxgram.v and FMsnprintfPf.v that both
   files read differ only in module paths (fuzz_preset -> fuzz_manifest, lib/A/PSnpBz -> lib/A/Bz,
   lib/Reusable/FMsnprintfPf -> lib/A/FMsnprintfPf) and header comments. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A Require Import I_pcxgram.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFPf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import FMpfStep RT_pf_sh.
Import ListNotations.
Open Scope Z_scope.

Lemma pcom_pcx_arm_Pc : pcom_pcx_arm Pc.
Proof.
  intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
  injection H as <- <-. split.
  - intros n W. exists (1 + n)%nat. cbn [pf_code app map pcx_walk]. cbn. rewrite W. reflexivity.
  - cbn [pf_code pc_cin1 app map]. cbn. reflexivity.
Qed.
