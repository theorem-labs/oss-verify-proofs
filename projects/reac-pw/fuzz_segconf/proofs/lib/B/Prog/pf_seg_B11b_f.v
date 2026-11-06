(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the FUNCTIONAL facts of segment
   B11b's join loop (the B11b segment lane of the image-B G3 walk owner, 2026-10-30). proves no function (kind: list computations).
   ADAPTED from the image-A G3 walk owner's image-A file lib/A/Prog/pf_a11b_f.v (commit b771066056fa, an
   image-A segment lane): the same computations over pf_seg_B11b_d.v's pb11_J / pb11_kn (A's pf_J / pf_kn), the literal
   addresses checked against image B's map SegInstB.seg_litA_rc (.rodata does not move between A and B: "%s%s"
   0x21820, "|" 0x21840, "" 0x21860, F_badmodel 0x21880, the B excerpt's .str.17 / .str.18 / .str.19 at 0x88b98 /
   0x88b20 / 0x88b2c).

   The loop at 0x88b14 joins the eleven tokens of the box-model table into known[240]:
     for (ti = 0; ti < ntok && kn + 2 < sizeof known; ti++)
       kn += snprintf(known + kn, sizeof known - kn, "%s%s", ti ? "|" : "", tab[ti].token);
   and SegModel.known_go is its model. Every proof here is a list computation: no image, no machine state. The
   plain walk of the same C proves the same facts (the unit owner's lib/Prog/pf_p7_lemmas.v p7_J / p7_kn / p7_J_11). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB
  reac_segconf_parse_file_c pf_seg_B11b_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** Two reflections, so that every fact of a pass is one `vm_compute` *)
Lemma pb11_nin0_of : forall l : list Z, existsb (Z.eqb 0) l = false -> ~ In 0 l.
Proof.
  induction l as [|x l IH]; intros H Hin; [exact Hin|].
  cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
  destruct Hin as [->|Hin]; [rewrite Z.eqb_refl in H1; discriminate | exact (IH H2 Hin)].
Qed.

Lemma pb11_bytepos_of : forall l : list Z,
  forallb (fun x => (0 <? x) && (x <? 256)) l = true -> Forall (fun x => 0 < x < 256) l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|].
  cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [Ha Hb]. apply Z.ltb_lt in Ha. apply Z.ltb_lt in Hb.
  constructor; [lia | exact (IH H2)].
Qed.

Lemma pb11_bytenn_of : forall l : list Z,
  forallb (fun x => (0 <=? x) && (x <? 256)) l = true -> Forall (fun x => 0 <= x < 256) l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|].
  cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [Ha Hb]. apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
  constructor; [lia | exact (IH H2)].
Qed.

(** ** The lengths of the eleven prefixes *)
Definition pb11_kns : list Z := [0; 5; 11; 18; 30; 36; 42; 49; 56; 63; 70; 77].

Lemma pb11_kn_nth : forall ti, (ti <= 11)%nat -> pb11_kn ti = nth ti pb11_kns 0.
Proof. intros ti Hti. do 12 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pb11_kns_bounded : Forall (fun z => 0 <= z <= 77) pb11_kns.
Proof. unfold pb11_kns. repeat (apply Forall_cons; [lia|]). apply Forall_nil. Qed.

Lemma pb11_kn_bound : forall ti, (ti <= 11)%nat -> 0 <= pb11_kn ti <= 77.
Proof.
  intros ti Hti. rewrite (pb11_kn_nth ti Hti).
  destruct (Nat.lt_ge_cases ti (length pb11_kns)) as [Hlt|Hge].
  - apply (proj1 (Forall_forall _ _) pb11_kns_bounded). apply nth_In. exact Hlt.
  - rewrite nth_overflow by exact Hge. lia.
Qed.

Lemma pb11_kn_0 : pb11_kn 0 = 0.
Proof. vm_compute. reflexivity. Qed.

(* the back edge `bltu kn + 2, 240` of the loop, and the model's own guard *)
Lemma pb11_kn_back : forall ti, (ti <= 11)%nat -> pb11_kn ti + 2 < 240.
Proof. intros ti Hti. pose proof (pb11_kn_bound ti Hti). lia. Qed.

(** ** One pass: the text it renders, that it is not cut, and the step of the join *)
Lemma pb11_fmt_ss : forall ti, (ti <= 10)%nat -> fmt F_ss (pb11_args ti) = pb11_sep ti ++ pb11_tok ti.
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pb11_snp_full : forall ti, (ti <= 10)%nat ->
  snprintf_s (240 - pb11_kn ti) F_ss (pb11_args ti) = fmt F_ss (pb11_args ti).
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pb11_snp_r : forall ti, (ti <= 10)%nat ->
  snprintf_r F_ss (pb11_args ti) = Z.of_nat (length (pb11_sep ti ++ pb11_tok ti)).
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pb11_J_step : forall ti, (ti <= 10)%nat -> pb11_J (S ti) = pb11_J ti ++ fmt F_ss (pb11_args ti).
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pb11_kn_step : forall ti, (ti <= 10)%nat -> pb11_kn (S ti) = pb11_kn ti + snprintf_r F_ss (pb11_args ti).
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

(** ** The eleventh pass leaves SegModel.known *)
Lemma pb11_J_11 : pb11_J 11 = known.
Proof. vm_compute. reflexivity. Qed.

Lemma pb11_known_len : length known = 77%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma pb11_J_nulfree : forall ti, (ti <= 11)%nat -> ~ In 0 (pb11_J ti).
Proof.
  intros ti Hti. apply pb11_nin0_of.
  do 12 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma pb11_J_byte : forall ti, (ti <= 11)%nat -> Forall (fun x => 0 <= x < 256) (pb11_J ti).
Proof.
  intros ti Hti. apply pb11_bytenn_of.
  do 12 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma pb11_known_nulfree : ~ In 0 known.
Proof. apply pb11_nin0_of. vm_compute. reflexivity. Qed.

(** ** The separator and the token of a pass *)
Lemma pb11_sep_0 : pb11_sep 0 = [].
Proof. reflexivity. Qed.
Lemma pb11_sep_S : forall ti, pb11_sep (S ti) = [124].
Proof. reflexivity. Qed.
Lemma pb11_sep_nulfree : forall ti, ~ In 0 (pb11_sep ti).
Proof. intros [|ti]; apply pb11_nin0_of; reflexivity. Qed.
Lemma pb11_sep_len : forall ti, (length (pb11_sep ti) <= 1)%nat.
Proof. intros [|ti]; cbn; lia. Qed.
Lemma pb11_sep_byte : forall ti, Forall (fun x => 0 < x < 256) (pb11_sep ti).
Proof. intros [|ti]; apply pb11_bytepos_of; reflexivity. Qed.

Definition pb11_tlens : list nat := [5; 5; 6; 11; 5; 5; 6; 6; 6; 6; 6]%nat.
Lemma pb11_tok_len_nth : forall ti, (ti <= 10)%nat -> length (pb11_tok ti) = nth ti pb11_tlens 0%nat.
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.
Lemma pb11_tlens_bounded : Forall (fun k => (5 <= k <= 11)%nat) pb11_tlens.
Proof. unfold pb11_tlens. repeat (apply Forall_cons; [lia|]). apply Forall_nil. Qed.
Lemma pb11_tok_len : forall ti, (ti <= 10)%nat -> (5 <= length (pb11_tok ti) <= 11)%nat.
Proof.
  intros ti Hti. rewrite (pb11_tok_len_nth ti Hti).
  destruct (Nat.lt_ge_cases ti (length pb11_tlens)) as [Hlt|Hge].
  - apply (proj1 (Forall_forall _ _) pb11_tlens_bounded). apply nth_In. exact Hlt.
  - exfalso. unfold pb11_tlens in Hge. cbn [length] in Hge. lia.
Qed.
Lemma pb11_tok_nulfree : forall ti, (ti <= 10)%nat -> ~ In 0 (pb11_tok ti).
Proof.
  intros ti Hti. apply pb11_nin0_of.
  do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma pb11_tok_byte : forall ti, (ti <= 10)%nat -> Forall (fun x => 0 < x < 256) (pb11_tok ti).
Proof.
  intros ti Hti. apply pb11_bytepos_of.
  do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia.
Qed.

(* the table's row ti holds exactly pb11_tok ti (seg_spec.cat_tok_nth ties the image's bytes to cat_toks) *)
Lemma pb11_tok_cat : forall ti, (ti < 11)%nat -> seg_spec.zs (pin_spec.tok_bytes ti) = pb11_tok ti.
Proof.
  intros ti Hti. unfold pb11_tok. apply seg_spec.cat_tok_nth. unfold pin_spec.CAT_N. exact Hti.
Qed.

(** ** The literals the loop and the refusal pass to the interceptors, and their addresses *)
Lemma pb11_lit_ss : seg_litA_rc F_ss = 0x21820.
Proof. vm_compute. reflexivity. Qed.
Lemma pb11_lit_bar : seg_litA_rc [124] = 0x21840.
Proof. vm_compute. reflexivity. Qed.
Lemma pb11_lit_empty : seg_litA_rc [] = 0x21860.
Proof. vm_compute. reflexivity. Qed.
Lemma pb11_lit_badmodel : seg_litA_rc F_badmodel = 0x21880.
Proof. vm_compute. reflexivity. Qed.

Lemma pb11_in_lits_ss : In F_ss PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma pb11_in_lits_bar : In [124] PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma pb11_in_lits_empty : In (@nil Z) PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma pb11_in_lits_badmodel : In F_badmodel PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma pb11_in_lits_sep : forall ti, In (pb11_sep ti) PARSE_FILE_LITS.
Proof. intros [|ti]; [exact pb11_in_lits_empty | exact pb11_in_lits_bar]. Qed.

(** ** The refusal: its format is one of refuse's seventeen, and its three arguments are all strings *)
Lemma pb11_badmodel_fmt : In F_badmodel seg_spec.REFUSE_FORMATS.
Proof. unfold seg_spec.REFUSE_FORMATS. cbn [In]. tauto. Qed.

Lemma pb11_badmodel_kinds : forall nm val k : list Z,
  seg_spec.conv_kinds F_badmodel = map seg_spec.arg_is_s [AS nm; AS val; AS k].
Proof. intros nm val k. vm_compute. reflexivity. Qed.
