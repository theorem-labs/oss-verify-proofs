(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMpfArmPdSeam.v (a working branch 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMpfArmPdSeam.table). *)
(* R-1 W9 (a Theorem Labs lane): the conversion %d (Pd) at the seam, on W0's per-piece arms (FMgxaSeamPf.v :98-111). The renderer
   equations pt_pf_digits_d / pt_pf_dec_d are fuzz_disco's pt_pf_digits / pt_pf_dec (a working branch
   5a2af4f2707 lib/A/FMgxaSeamPf.v Section CoveredD's preamble), copied; the three arms restate CoveredD's Pd case in
   W0's form (one step of the renderer, FMpfStep.v pf_step). New file; nothing else is edited. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMpfStep FMgxaSeamPf.
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
