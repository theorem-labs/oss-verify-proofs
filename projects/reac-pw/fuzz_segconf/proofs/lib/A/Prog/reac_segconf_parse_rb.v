(* reac-pw/fuzz_segconf: how many refusals one call of the reader's parse counts (SegModel.v only, no image), for
   the ASan walk of reac_segconf_parse (lib/A/Prog/reac_segconf_parse.v): cross_check_pre asks
   rc_refused + 64 < 2 ^ 32 of the state parse_file returns. Copied by the G3 walk owner from the plain-build walk owner's plain
   lib/Spec/SegRefusedBound.v (commit db8c4beebf62), whose SegModel.v is the one in this tree
   (git diff db8c4beebf62 45ef51243c87 -- lib/Spec/SegModel.v is empty); module paths unchanged, names unchanged.
   Every line of SegModel.r_lines adds 0 or 1 to rc_refused, so r_parse_file adds at most length (lines text),
   and with SegModel.lines_props (at most length text lines for a NUL-free text) and reader_pre's bounds (a text
   of at most 65535 bytes, rc_refused + 2 ^ 17 < 2 ^ 32) the count stays 64 below 2 ^ 32. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
Import ListNotations.
Open Scope Z_scope.

Lemma refuse_refused c line f a : rc_refused (refuse c line f a) = rc_refused c + 1.
Proof.
  unfold refuse. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma r_upd_refused c i f : rc_refused (r_upd c i f) = rc_refused c.
Proof. reflexivity. Qed.

Lemma seg_get_refused c name : rc_refused (fst (seg_get c name)) = rc_refused c.
Proof.
  unfold seg_get.
  repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; reflexivity.
Qed.

(** Split every [if] and [match] of a branch of the parse; a [seg_get] keeps its count. *)
Ltac rb_split :=
  repeat match goal with
  | |- context [seg_get ?c ?nm] =>
      let G := fresh "G" in
      pose proof (seg_get_refused c nm) as G; revert G;
      destruct (seg_get c nm) as [? [[? ?]|]]; cbn [fst]; intros G
  | |- context [match ?x with _ => _ end] => destruct x
  end.

Ltac rb_leaf := cbn [fst snd] in *; rewrite ?r_upd_refused, ?refuse_refused; lia.

Lemma r_header_refused c cn n line : rc_refused (fst (fst (r_header c cn n line))) <= rc_refused c + 1.
Proof. unfold r_header. cbv zeta. rb_split; rb_leaf. Qed.

Lemma r_key_refused c cur cn n line : rc_refused (fst (fst (r_key c cur cn n line))) <= rc_refused c + 1.
Proof. unfold r_key. cbv zeta. rb_split; rb_leaf. Qed.

Lemma r_line_refused c cur cn n l : rc_refused (fst (fst (r_line c cur cn n l))) <= rc_refused c + 1.
Proof.
  unfold r_line. cbv zeta.
  destruct (512 <=? length l)%nat; [cbn [fst]; rewrite refuse_refused; lia|].
  destruct (hd0 (r_trim (r_strip_comment l)) =? 0); [cbn [fst]; lia|].
  destruct (hd0 (r_trim (r_strip_comment l)) =? LBR); [apply r_header_refused | apply r_key_refused].
Qed.

Lemma r_lines_refused ls : forall st n,
  rc_refused (fst (fst (r_lines st n ls))) <= rc_refused (fst (fst st)) + Z.of_nat (length ls).
Proof.
  induction ls as [|l r IH]; intros [[c cur] nm] n; cbn [r_lines fst length].
  - lia.
  - pose proof (IH (r_line c cur nm (n + 1) l) (n + 1)) as H1.
    pose proof (r_line_refused c cur nm (n + 1) l) as H2.
    lia.
Qed.

Lemma r_parse_file_refused c text label :
  rc_refused (fst (r_parse_file c text label)) <= rc_refused c + Z.of_nat (length (lines text)).
Proof.
  unfold r_parse_file. cbv zeta.
  match goal with |- context [r_lines ?st ?n ?ls] =>
    pose proof (r_lines_refused ls st n) as H; revert H; destruct (r_lines st n ls) as [[c2 cur] nm]
  end.
  cbn [fst rc_refused]. intros H. exact H.
Qed.

(** The bound reac_segconf_parse hands to cross_check. *)
Lemma r_parse_file_refused_bound c text label :
  nulfree text -> (length text <= 65535)%nat -> rc_refused c + 2 ^ 17 < 2 ^ 32 ->
  rc_refused (fst (r_parse_file c text label)) + 64 < 2 ^ 32.
Proof.
  intros N L R. pose proof (r_parse_file_refused c text label) as H.
  destruct (lines_props text N) as [_ LL].
  assert (L' : Z.of_nat (length text) <= 65535) by (apply Nat2Z.inj_le in L; exact L).
  change (2 ^ 17) with 131072 in R. change (2 ^ 32) with 4294967296 in R |- *. clear L. lia.
Qed.

(** reac_segconf_parse's model is parse_file's, then cross_check of the block (SegModel.r_parse). *)
Lemma r_parse_snd rc s : snd (r_parse rc s) = snd (r_parse_file rc s (Some S_base)).
Proof. unfold r_parse. destruct (r_parse_file rc s (Some S_base)). reflexivity. Qed.
Lemma r_parse_fst rc s : fst (r_parse rc s) = cross_check (fst (r_parse_file rc s (Some S_base))).
Proof. unfold r_parse. destruct (r_parse_file rc s (Some S_base)). reflexivity. Qed.
