(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMpfArmPdSeam.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* The conversion %d (Pd) at the seam, on the per-piece arms (FMgxaSeamPf.v :98-111). The renderer
   equations pt_pf_digits_d / pt_pf_dec_d are fuzz_disco's pt_pf_digits / pt_pf_dec (fuzz_disco's
   lib/A/FMgxaSeamPf.v Section CoveredD's preamble), copied; the three arms restate CoveredD's Pd case in
   the per-piece arm form (one step of the renderer, FMpfStep.v pf_step). New file; nothing else is edited. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFPf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import FMpfStep FMgxaSeamPf.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the renderer equation (fuzz_disco's, copied) ---- *)
Lemma pt_pf_digits_d : forall fuel x acc, PT.pf_digits fuel x acc = pf_digits fuel x acc.
Proof.
induction fuel as [|f IH]; intros x acc; [reflexivity|].
cbn [PT.pf_digits pf_digits]. destruct (x <? 10); [reflexivity | apply IH].
Qed.
Lemma pt_pf_dec_d : forall v, PT.pf_dec v = pf_dec v.
Proof. intros v. unfold PT.pf_dec, pf_dec. rewrite !pt_pf_digits_d. reflexivity. Qed.

(* ---- the three arms at Pd ---- *)
Lemma seam_text_arm_pd : seam_text_arm Pd.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. cbn [pt_piece map pt_arg PT.pf_text]. rewrite pt_pf_dec_d.
destruct (PT.pf_text qs (map pt_arg a'')); reflexivity.
Qed.

Lemma seam_pargs_arm_pd : seam_pargs_arm Pd.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. exists [AInt v], [PA_i v].
split; [reflexivity|]. split; [constructor; [left; reflexivity | constructor] | reflexivity].
Qed.

(* every digit pf_digits writes is a byte, for a nonnegative number *)
Lemma pf_digits_bytes : forall fuel x acc, 0 <= x -> Forall (fun b => 0 <= b < 256) acc ->
  Forall (fun b => 0 <= b < 256) (pf_digits fuel x acc).
Proof.
induction fuel as [|f IH]; intros x acc Hx Hacc; [exact Hacc|].
cbn [pf_digits]. destruct (x <? 10) eqn:E.
- apply Z.ltb_lt in E. constructor; [lia | exact Hacc].
- apply Z.ltb_ge in E. apply IH; [apply Z.div_pos; lia|].
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)). constructor; [lia | exact Hacc].
Qed.

Lemma seam_bytes_arm_pd : seam_bytes_arm Pd.
Proof.
intros args c a' _ _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- _. unfold pf_dec. destruct (v <? 0) eqn:E.
- apply Z.ltb_lt in E. constructor; [lia|]. apply pf_digits_bytes; [lia | constructor].
- apply Z.ltb_ge in E. apply pf_digits_bytes; [lia | constructor].
Qed.

(* ---- control: "%d" at -42 renders "-42" through the arm on both copies ---- *)
Lemma seam_pd_control :
  pf_parse [37; 100] = Some [Pd] /\ pf_text [Pd] [AInt (-42)] = Some [45; 52; 50] /\
  PT.pf_text (map pt_piece [Pd]) (map pt_arg [AInt (-42)]) = Some [45; 52; 50].
Proof.
split; [reflexivity|]. split; [reflexivity|].
apply (pt_text_eqP (fun p => p = Pd) (fun p Hp => eq_ind_r seam_text_arm seam_text_arm_pd Hp));
  [repeat constructor | reflexivity].
Qed.
