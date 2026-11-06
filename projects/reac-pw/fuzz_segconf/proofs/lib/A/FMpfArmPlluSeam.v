(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMpfArmPlluSeam.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* The conversion %llu (Pllu) at the seam, on the per-piece arms (FMgxaSeamPf.v :98-111). The
   renderer equations are fuzz_disco's pt_pf_digits / pt_pf_udec (fuzz_disco's lib/A/FMgxaSeamPf.v
   Section CoveredD's preamble), copied; the three arms restate CoveredD's Pllu case in the per-piece arm form.
   The bytes arm uses pf_arg_fit's 0 <= u (pf_udec of a negative u is not a byte). New file; nothing else is edited. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import FMpfStep FMgxaSeamPf.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the renderer equation (fuzz_disco's, copied) ---- *)
Lemma pt_pf_digits_llu : forall fuel x acc, PT.pf_digits fuel x acc = pf_digits fuel x acc.
Proof.
induction fuel as [|f IH]; intros x acc; [reflexivity|].
cbn [PT.pf_digits pf_digits]. destruct (x <? 10); [reflexivity | apply IH].
Qed.
Lemma pt_pf_udec_llu : forall u, PT.pf_udec u = pf_udec u.
Proof. intros u. unfold PT.pf_udec, pf_udec. apply pt_pf_digits_llu. Qed.

(* ---- the three arms at Pllu ---- *)
Lemma seam_text_arm_pllu : seam_text_arm Pllu.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. cbn [pt_piece map pt_arg PT.pf_text]. rewrite pt_pf_udec_llu.
destruct (PT.pf_text qs (map pt_arg a'')); reflexivity.
Qed.

Lemma seam_pargs_arm_pllu : seam_pargs_arm Pllu.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. exists [AU64 u], [PA_ull u].
split; [reflexivity|]. split; [constructor; [left; reflexivity | constructor] | reflexivity].
Qed.

Lemma pf_digits_bytes_llu : forall fuel x acc, 0 <= x -> Forall (fun b => 0 <= b < 256) acc ->
  Forall (fun b => 0 <= b < 256) (pf_digits fuel x acc).
Proof.
induction fuel as [|f IH]; intros x acc Hx Hacc; [exact Hacc|].
cbn [pf_digits]. destruct (x <? 10) eqn:E.
- apply Z.ltb_lt in E. constructor; [lia | exact Hacc].
- apply Z.ltb_ge in E. apply IH; [apply Z.div_pos; lia|].
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)). constructor; [lia | exact Hacc].
Qed.

Lemma seam_bytes_arm_pllu : seam_bytes_arm Pllu.
Proof.
intros args c a' _ HF H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- _. inversion HF as [|? ? Hu _]; subst. cbn [pf_arg_fit] in Hu.
unfold pf_udec. apply pf_digits_bytes_llu; [lia | constructor].
Qed.

(* ---- control: "%llu" at 2^64 - 1 renders its 20 digits through the arm on both copies ---- *)
Lemma seam_pllu_control :
  pf_parse [37; 108; 108; 117] = Some [Pllu] /\
  pf_text [Pllu] [AU64 18446744073709551615] = Some [49; 56; 52; 52; 54; 55; 52; 52; 48; 55; 51; 55; 48; 57; 53; 53; 49; 54; 49; 53] /\
  PT.pf_text (map pt_piece [Pllu]) (map pt_arg [AU64 18446744073709551615])
    = Some [49; 56; 52; 52; 54; 55; 52; 52; 48; 55; 51; 55; 48; 57; 53; 53; 49; 54; 49; 53].
Proof.
split; [reflexivity|]. split; [vm_compute; reflexivity|].
apply (pt_text_eqP (fun p => p = Pllu) (fun p Hp => eq_ind_r seam_text_arm seam_text_arm_pllu Hp));
  [repeat constructor | vm_compute; reflexivity].
Qed.
