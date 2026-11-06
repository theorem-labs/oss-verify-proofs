(** reac-pw/fuzz_segconf: facts the walks of reac_box_catalogue_by_token share, plain (Prog/reac_box_catalogue_by_token.v)
    and UBSan (U/Prog/reac_box_catalogue_by_token.v). Nothing here depends on a build: the table address [cat] is a
    variable.

    [row_ptr_by_token]: fuzz_catalogue_row's answer on the bytes sb (pin_spec.row_ptr, the first row whose token
    bytes are sb: row_scan with bytes_eqb (tok_bytes i)) is seg_spec.cat_ptr of the spine's by_token on their values
    (SegModel.row_go over cat_toks with the length test and leqb), when sb has no NUL; seg_spec.cat_toks_bytes ties
    cat_toks to tok_bytes. [cstr_cut]: a C string with any slack (seg_spec.cstr_at) is a C string with exactly the
    slack to the next 8-byte boundary (strlen's premise), less than 8 bytes, so the bytes it covers end below
    [lo + 8] when the string ends at or below [lo]. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** The lookup *)
Lemma stb_eqb : forall a b, bytes_eqb a b = leqb (zs a) (zs b).
Proof.
  unfold zs. induction a as [|x a IH]; intros [|y b]; cbn [bytes_eqb map leqb]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma stb_len_leqb : forall k t, ((length k =? length t)%nat && leqb k t) = leqb k t.
Proof.
  intros k t. destruct (leqb k t) eqn:E.
  - rewrite (leqb_len k t E), Nat.eqb_refl. reflexivity.
  - apply andb_false_r.
Qed.

Lemma stb_scan : forall n i sb,
  row_scan n i sb = row_go (map (fun j => zs (tok_bytes j)) (seq i n)) (zs sb) i.
Proof.
  induction n as [|n IH]; intros i sb; [reflexivity|].
  cbn [row_scan seq map row_go]. rewrite stb_len_leqb, <- stb_eqb, IH. reflexivity.
Qed.

Lemma stb_row_of : forall sb, row_of sb = cat_row (zs sb).
Proof.
  intros sb. unfold row_of, row_from, cat_row. rewrite <- cat_toks_bytes, Nat.sub_0_r. apply stb_scan.
Qed.

Lemma row_ptr_by_token : forall cat sb, ~ In 0 (zs sb) -> row_ptr cat sb = cat_ptr cat (by_token (zs sb)).
Proof.
  intros cat sb H. unfold row_ptr, by_token. rewrite (cut_nul_id (zs sb) H), <- stb_row_of.
  destruct (row_of sb); reflexivity.
Qed.

(** ** The string *)
Lemma stb_nonul : forall bs, ~ In 0 (zs bs) -> ~ In (Z_to_bv 8 0) bs.
Proof. intros bs H Hin. apply H. apply (in_map bv_unsigned) in Hin. exact Hin. Qed.

Lemma cstr_cut : forall segs m a s, cstr_at segs m a s ->
  exists bs sl, bytes_at segs m a (bs ++ Z_to_bv 8 0 :: sl) /\ zs bs = s /\ ~ In 0 s /\ ~ In (Z_to_bv 8 0) bs /\
    length bs = length s /\
    (- (a + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length sl) /\ Z.of_nat (length sl) < 8.
Proof.
  intros segs m a s (bs & sl & HB & Hz & Hn & Hsl). subst s.
  assert (Lz : length (zs bs) = length bs) by (unfold zs; apply length_map).
  rewrite Lz in Hsl.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length bs) + 1)) 8 ltac:(lia)) as Hk.
  remember (Z.to_nat ((- (a + Z.of_nat (length bs) + 1)) mod 8)) as k eqn:Ek.
  assert (Lk : length (firstn k sl) = k) by (rewrite length_firstn; lia).
  exists bs, (firstn k sl).
  split.
  { assert (E : bs ++ ZERO :: sl = (bs ++ Z_to_bv 8 0 :: firstn k sl) ++ skipn k sl).
    { rewrite <- app_assoc. cbn [app]. rewrite firstn_skipn. reflexivity. }
    rewrite E in HB. apply bytes_at_app in HB. exact (proj1 HB). }
  split; [reflexivity|]. split; [exact Hn|]. split; [apply stb_nonul, Hn|]. split; [symmetry; exact Lz|].
  rewrite Lk. split; lia.
Qed.
