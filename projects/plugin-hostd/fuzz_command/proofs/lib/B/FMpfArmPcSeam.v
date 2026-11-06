(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMpfArmPcSeam.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* The three SEAM ARMS of %c (Pc), in the per-piece arm form (FMgxaSeamPf.v seam_text_arm :98,
   seam_pargs_arm :104, seam_bytes_arm :111). Section CoveredP of FMgxaSeamPf.v and Section P of FMgxaSeam.v
   (fm_vfprintf_seamP) take them as ARM_text / ARM_pargs / ARM_bytes for a PK that holds Pc (AuditRcSeamCtl.v
   instantiates fm_vfprintf_seamP so). New file; no existing file is changed.

   Pc's step (FMpfStep.v pf_step) is `AInt v :: a' => Some ([v mod 256], a')`:
   - text: PT.pf_text's Pc arm (Printf_text.v:80) is `option_map (cons (v mod 256))`, the same body as pf_text's
     (FMsnprintfPf.v:75); it equals `option_map (app [v mod 256])` by conversion;
   - pargs: PT.pf_pargs takes Pc's AInt v as PA_i v (Printf_text.v:99), which is pt_parg (AInt v)
     (FMgxaSeamPf.v:49): the left disjunct of pt_parg_ok;
   - bytes: v mod 256 is a byte for every v (Z.mod_pos_bound), so this arm needs neither pf_code_ok nor
     pf_arg_fit. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFPf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import FMpfStep FMgxaSeamPf.
Import ListNotations.
Open Scope Z_scope.

Lemma seam_text_arm_c : seam_text_arm Pc.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. cbn [pt_piece map pt_arg PT.pf_text].
destruct (PT.pf_text qs (map pt_arg a'')); reflexivity.
Qed.

Lemma seam_pargs_arm_c : seam_pargs_arm Pc.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. exists [AInt v], [PA_i v].
split; [reflexivity|]. split; [constructor; [left; reflexivity | constructor] | reflexivity].
Qed.

Lemma seam_bytes_arm_c : seam_bytes_arm Pc.
Proof.
intros args c a' _ _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- _. constructor; [cbv beta; apply Z.mod_pos_bound; lia | constructor].
Qed.
