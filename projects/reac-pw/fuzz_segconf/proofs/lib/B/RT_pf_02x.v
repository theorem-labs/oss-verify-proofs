(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_02x.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* R1 row R-02x, PCOM arm: the conversion %02x (Px02) in ASan printf_common's scan, in W0-pcom's per-piece form
   (RT_pf_sh.v :122 pcom_pcx_arm). New file; RT_pf_sh.v is not edited.
   - pcom_pcx_arm_px02: one pcx_walk step reads %02x's code [37; 48; 50; 120] with the one argument it consumes: pcx_dir
     reads '0' as a flag, '2' as the width and 'x' as an int conversion (I_pcxgram.v pcx_flags / pcx_digits / pcx_conv),
     and the argument, pa_of (AInt v) = PA_i v, fits PK_int; its coverage entry is pc_cin1 Px02 = [None] (an int is never
     range-checked);
   - pf_pc_02x / pf_pc_02x_arms: fm's printf_common pieces (pf_fm_pc: literals, %s, %.*s) and %02x, each with its arm, so
     Section PcomK's pcx_K / pcomx_K and RT_pf_shU.v's pcom_shzK apply at PK := pf_pc_02x;
   - a NON-VACUITY control at fuzz_disco's own %02x format (fuzz_disco.c:592, .rodata 0x20f80 of the asan and the
     asan-ubsan image, the 29 bytes "%02x:%02x:%02x:%02x:%02x:%02x", read from the pinned image
     of libreac/fuzz_disco's ASan build, sha256 5e39150dd8104df9...): it parses to six Px02 pieces and five literals,
     renders a concrete MAC, and pcomx_K at pf_pc_02x accepts it with six None coverage entries; fm's pf_fm_pc does
     not cover it. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import I_pcxgram.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import FMpfStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import RT_pf_sh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---- the arm at %02x ---- *)
Lemma pcom_pcx_arm_px02 : pcom_pcx_arm Px02.
Proof.
  intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
  injection H as <- <-. split.
  - intros n W. exists (1 + n)%nat. cbn [pf_code app map pcx_walk]. cbn. rewrite W. reflexivity.
  - cbn [pf_code pc_cin1 app map]. cbn. reflexivity.
Qed.

(* ---- fm's printf_common pieces and %02x, each with its arm ---- *)
Definition pf_pc_02x (p : pf_piece) : Prop := match p with PLit _ | Ps | Pps | Px02 => True | _ => False end.

Lemma pf_pc_02x_of_fm : forall p, pf_fm_pc p -> pf_pc_02x p.
Proof. intros p Hp. destruct p; cbn in Hp |- *; tauto. Qed.

Lemma pf_pc_02x_arms : forall p, pf_pc_02x p -> pcom_pcx_arm p.
Proof.
  intros p Hp. destruct p; try (exfalso; exact Hp).
  - apply pcom_pcx_arm_lit.
  - exact pcom_pcx_arm_px02.
  - exact pcom_pcx_arm_ps.
  - exact pcom_pcx_arm_pps.
Qed.

(* ---- NON-VACUITY control: fuzz_disco's own %02x format (fuzz_disco.c:592, .rodata 0x20f80, both images) ---- *)
Definition disco_mac_fmt : list Z :=
  [37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58;
   37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120].
Definition disco_mac_ps : list pf_piece :=
  [Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02].
Definition disco_mac_args : list pf_arg := map AInt [0xde; 0xad; 0xbe; 0xef; 0x00; 0x01].
(* "de:ad:be:ef:00:01" *)
Definition disco_mac_text : list Z :=
  [100; 101; 58; 97; 100; 58; 98; 101; 58; 101; 102; 58; 48; 48; 58; 48; 49].

Lemma disco_mac_parse : pf_parse disco_mac_fmt = Some disco_mac_ps.
Proof. vm_compute. reflexivity. Qed.

Lemma disco_mac_pieces : Forall pf_pc_02x disco_mac_ps.
Proof. repeat constructor. Qed.

Lemma disco_mac_render : pf_text disco_mac_ps disco_mac_args = Some disco_mac_text.
Proof. vm_compute. reflexivity. Qed.

(* the arm bites: printf_common's walk accepts the format, and the six %02x arguments get one None entry each *)
Lemma disco_mac_pcomx :
  pcomx_ok (disco_mac_fmt ++ [0]) (map pa_of disco_mac_args) = true /\
  pcx_covs (length (disco_mac_fmt ++ [0])) (disco_mac_fmt ++ [0]) (map pa_of disco_mac_args) (pc_cinK disco_mac_ps)
  = [None; None; None; None; None; None].
Proof.
  destruct (pcomx_K pf_pc_02x pf_pc_02x_arms disco_mac_fmt disco_mac_ps disco_mac_args disco_mac_text
              disco_mac_parse disco_mac_pieces disco_mac_render) as [OK C].
  split; [exact OK|]. rewrite C. reflexivity.
Qed.

(* and fm's own predicate does not cover it: the arm is new *)
Lemma disco_mac_not_fm : ~ Forall pf_fm_pc disco_mac_ps.
Proof. intros H. inversion H as [|? ? Hp _]. exact Hp. Qed.
