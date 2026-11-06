(* reac-pw/fuzz_segconf, image A: the FUNCTIONAL facts of segment A11b's join loop (part of segment A11b's proof, by
   the G3 walk owner, 2026-10-30), shared by the three sub-proofs of A11b.

   The loop at 0x8865c joins the eleven tokens of the box-model table into known[240]:
     for (ti = 0; ti < ntok && kn + 2 < sizeof known; ti++)
       kn += snprintf(known + kn, sizeof known - kn, "%s%s", ti ? "|" : "", tab[ti].token);
   and SegModel.known_go is its model (SegModel.v:623-634). pf_a11b_d.v's pf_J ti is the join of the first ti
   tokens and pf_kn ti its length; this file proves, by computation on the closed list SegModel.cat_toks, the
   facts the walk needs about them: the table of the eleven lengths, the step of one pass, that no pass is cut
   by the 240-byte bound, that the eleventh pass leaves SegModel.known, and the literal addresses of the three
   texts the loop and the refusal pass to the interceptors.

   Every proof here is a list computation: no image, no machine state. The plain walk of the same C proves the
   same facts (the plain-build walk owner's lib/Prog/pf_p7_lemmas.v:179-248 at commit cfdd99183965, p7_J / p7_kn /
   p7_sep / p7_tok / p7_kn_nth / p7_J_step / p7_J_11 / p7_known_len). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA
  reac_segconf_parse_file_c pf_a11b_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** Two reflections, so that every fact of a pass is one `vm_compute` *)
Lemma pf_nin0_of : forall l : list Z, existsb (Z.eqb 0) l = false -> ~ In 0 l.
Proof.
  induction l as [|x l IH]; intros H Hin; [exact Hin|].
  cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
  destruct Hin as [->|Hin]; [rewrite Z.eqb_refl in H1; discriminate | exact (IH H2 Hin)].
Qed.

Lemma pf_bytepos_of : forall l : list Z,
  forallb (fun x => (0 <? x) && (x <? 256)) l = true -> Forall (fun x => 0 < x < 256) l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|].
  cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [Ha Hb]. apply Z.ltb_lt in Ha. apply Z.ltb_lt in Hb.
  constructor; [lia | exact (IH H2)].
Qed.

Lemma pf_bytenn_of : forall l : list Z,
  forallb (fun x => (0 <=? x) && (x <? 256)) l = true -> Forall (fun x => 0 <= x < 256) l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|].
  cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
  apply andb_true_iff in H1 as [Ha Hb]. apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
  constructor; [lia | exact (IH H2)].
Qed.

(** ** The lengths of the eleven prefixes *)
Definition pf_kns : list Z := [0; 5; 11; 18; 30; 36; 42; 49; 56; 63; 70; 77].

Lemma pf_kn_nth : forall ti, (ti <= 11)%nat -> pf_kn ti = nth ti pf_kns 0.
Proof. intros ti Hti. do 12 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pf_kns_bounded : Forall (fun z => 0 <= z <= 77) pf_kns.
Proof. unfold pf_kns. repeat (apply Forall_cons; [lia|]). apply Forall_nil. Qed.

Lemma pf_kn_bound : forall ti, (ti <= 11)%nat -> 0 <= pf_kn ti <= 77.
Proof.
  intros ti Hti. rewrite (pf_kn_nth ti Hti).
  destruct (Nat.lt_ge_cases ti (length pf_kns)) as [Hlt|Hge].
  - apply (proj1 (Forall_forall _ _) pf_kns_bounded). apply nth_In. exact Hlt.
  - rewrite nth_overflow by exact Hge. lia.
Qed.

Lemma pf_kn_0 : pf_kn 0 = 0.
Proof. vm_compute. reflexivity. Qed.

(* the back edge `bltu kn + 2, 240` of the loop, and the model's own guard *)
Lemma pf_kn_back : forall ti, (ti <= 11)%nat -> pf_kn ti + 2 < 240.
Proof. intros ti Hti. pose proof (pf_kn_bound ti Hti). lia. Qed.

(** ** One pass: the text it renders, that it is not cut, and the step of the join *)
Lemma pf_fmt_ss : forall ti, (ti <= 10)%nat -> fmt F_ss (pf_args ti) = pf_sep ti ++ pf_tok ti.
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pf_snp_full : forall ti, (ti <= 10)%nat ->
  snprintf_s (240 - pf_kn ti) F_ss (pf_args ti) = fmt F_ss (pf_args ti).
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pf_snp_r : forall ti, (ti <= 10)%nat ->
  snprintf_r F_ss (pf_args ti) = Z.of_nat (length (pf_sep ti ++ pf_tok ti)).
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pf_J_step : forall ti, (ti <= 10)%nat -> pf_J (S ti) = pf_J ti ++ fmt F_ss (pf_args ti).
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma pf_kn_step : forall ti, (ti <= 10)%nat -> pf_kn (S ti) = pf_kn ti + snprintf_r F_ss (pf_args ti).
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

(** ** The eleventh pass leaves SegModel.known *)
Lemma pf_J_11 : pf_J 11 = known.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_J_nulfree : forall ti, (ti <= 11)%nat -> ~ In 0 (pf_J ti).
Proof.
  intros ti Hti. apply pf_nin0_of.
  do 12 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma pf_J_byte : forall ti, (ti <= 11)%nat -> Forall (fun x => 0 <= x < 256) (pf_J ti).
Proof.
  intros ti Hti. apply pf_bytenn_of.
  do 12 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia.
Qed.

(** ** The separator and the token of a pass *)
Lemma pf_sep_0 : pf_sep 0 = [].
Proof. reflexivity. Qed.
Lemma pf_sep_S : forall ti, pf_sep (S ti) = [124].
Proof. reflexivity. Qed.
Lemma pf_sep_nulfree : forall ti, ~ In 0 (pf_sep ti).
Proof. intros [|ti]; apply pf_nin0_of; reflexivity. Qed.
Lemma pf_sep_len : forall ti, (length (pf_sep ti) <= 1)%nat.
Proof. intros [|ti]; cbn; lia. Qed.
Lemma pf_sep_byte : forall ti, Forall (fun x => 0 < x < 256) (pf_sep ti).
Proof. intros [|ti]; apply pf_bytepos_of; reflexivity. Qed.

Definition pf_tlens : list nat := [5; 5; 6; 11; 5; 5; 6; 6; 6; 6; 6]%nat.
Lemma pf_tok_len_nth : forall ti, (ti <= 10)%nat -> length (pf_tok ti) = nth ti pf_tlens 0%nat.
Proof. intros ti Hti. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.
Lemma pf_tlens_bounded : Forall (fun k => (5 <= k <= 11)%nat) pf_tlens.
Proof. unfold pf_tlens. repeat (apply Forall_cons; [lia|]). apply Forall_nil. Qed.
Lemma pf_tok_len : forall ti, (ti <= 10)%nat -> (5 <= length (pf_tok ti) <= 11)%nat.
Proof.
  intros ti Hti. rewrite (pf_tok_len_nth ti Hti).
  destruct (Nat.lt_ge_cases ti (length pf_tlens)) as [Hlt|Hge].
  - apply (proj1 (Forall_forall _ _) pf_tlens_bounded). apply nth_In. exact Hlt.
  - exfalso. unfold pf_tlens in Hge. cbn [length] in Hge. lia.
Qed.
Lemma pf_tok_nulfree : forall ti, (ti <= 10)%nat -> ~ In 0 (pf_tok ti).
Proof.
  intros ti Hti. apply pf_nin0_of.
  do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma pf_tok_byte : forall ti, (ti <= 10)%nat -> Forall (fun x => 0 < x < 256) (pf_tok ti).
Proof.
  intros ti Hti. apply pf_bytepos_of.
  do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia.
Qed.

(* the table's row ti holds exactly pf_tok ti (seg_spec.cat_tok_nth ties the image's bytes to cat_toks) *)
Lemma pf_tok_cat : forall ti, (ti < 11)%nat -> seg_spec.zs (pin_spec.tok_bytes ti) = pf_tok ti.
Proof.
  intros ti Hti. unfold pf_tok. apply seg_spec.cat_tok_nth. unfold pin_spec.CAT_N. exact Hti.
Qed.

(** ** The literals the loop and the refusal pass to the interceptors, and their addresses *)
Lemma pf_lit_ss : seg_litA_rc F_ss = 0x21820.
Proof. vm_compute. reflexivity. Qed.
Lemma pf_lit_bar : seg_litA_rc [124] = 0x21840.
Proof. vm_compute. reflexivity. Qed.
Lemma pf_lit_empty : seg_litA_rc [] = 0x21860.
Proof. vm_compute. reflexivity. Qed.
Lemma pf_lit_badmodel : seg_litA_rc F_badmodel = 0x21880.
Proof. vm_compute. reflexivity. Qed.

Lemma pf_in_lits_ss : In F_ss PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma pf_in_lits_bar : In [124] PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma pf_in_lits_empty : In (@nil Z) PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma pf_in_lits_badmodel : In F_badmodel PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma pf_in_lits_sep : forall ti, In (pf_sep ti) PARSE_FILE_LITS.
Proof. intros [|ti]; [exact pf_in_lits_empty | exact pf_in_lits_bar]. Qed.

(** ** The refusal: its format is one of refuse's seventeen, and its three arguments are all strings *)
Lemma pf_badmodel_fmt : In F_badmodel seg_spec.REFUSE_FORMATS.
Proof. unfold seg_spec.REFUSE_FORMATS. cbn [In]. tauto. Qed.

Lemma pf_badmodel_kinds : forall nm val k : list Z,
  seg_spec.conv_kinds F_badmodel = map seg_spec.arg_is_s [AS nm; AS val; AS k].
Proof. intros nm val k. vm_compute. reflexivity. Qed.
