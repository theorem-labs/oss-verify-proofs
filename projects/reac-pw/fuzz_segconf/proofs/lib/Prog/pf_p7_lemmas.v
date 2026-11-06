(** Image-free helpers the walk of piece P7 (the model key) of reac_segconf_parse_file needs beyond
    lib/Prog/pfC_facts.v: the spine step of r_key's model branch, the fold into low[24]
    (R:254-256), the eleven equations of the join loop of R:258-263, and the byte-block patch lemma that reads a
    block back from the memory a call left.

    Nothing here mentions an image: the memory lemma takes the build's segment list as a Section variable, so
    lib/Prog/pf_p7.v (plain) and lib/U/Prog/pf_p7.v (UBSan) share this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
Import ListNotations.
Open Scope Z_scope.

(** * 1. Small list facts *)

Lemma p7_nth_error_some : forall {A} (l : list A) (d : A) i, (i < length l)%nat -> nth_error l i = Some (nth i l d).
Proof.
  intros A l d. induction l as [|x l IH]; intros [|i] H; cbn [length] in H; try lia; cbn [nth_error nth].
  - reflexivity.
  - apply IH. cbn [length] in H. lia.
Qed.

Lemma p7_zbyte_forallb : forall l, forallb (fun x => (0 <=? x) && (x <? 256)) l = true ->
  Forall (fun x => 0 <= x < 256) l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|]. cbn [forallb] in H.
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [H0 H1].
  constructor; [apply Z.leb_le in H0; apply Z.ltb_lt in H1; lia | exact (IH H2)].
Qed.

Lemma p7_firstn1_skipn : forall {A} (bs : list A) i (b : A), nth_error bs i = Some b -> firstn 1 (skipn i bs) = [b].
Proof.
  intros A bs. induction bs as [|x bs IH]; intros [|i] b H; cbn [nth_error skipn] in H; try discriminate.
  - cbn [skipn firstn]. inversion H; subst. reflexivity.
  - cbn [skipn]. apply IH. exact H.
Qed.

(** * 2. A block read back after a call that changed it only inside one window *)

Section Patch.
Variable segs : list Segment.

(** One byte read from a block, in the shape [step]'s load automation folds. *)
Lemma p7_read1 : forall (m : word -> option byte) (a : Z) (bs : list byte) (i : nat) (b : byte),
  bytes_at segs m a bs -> nth_error bs i = Some b ->
  ov_read_bytes segs m (wa (a + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m a bs i b HB HN.
  assert (Hi : (i < length bs)%nat) by (apply (proj1 (nth_error_Some bs i)); rewrite HN; discriminate).
  rewrite (bytes_at_read segs m a bs (Z.of_nat i) 1%nat HB ltac:(lia) ltac:(rewrite Nat2Z.id; lia)).
  rewrite Nat2Z.id, (p7_firstn1_skipn bs i b HN). reflexivity.
Qed.

Lemma p7_bytes_patch : forall (W : list ivl) (m m' : word -> option byte) (a : Z) (bs : list byte) (k : Z)
    (p : list byte),
  bytes_at segs m a bs -> munch W m m' -> bytes_at segs m' (a + k) p ->
  0 <= k -> (Z.to_nat k + length p <= length bs)%nat ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> ~ (a + k <= x < a + k + Z.of_nat (length p)) -> outside W x) ->
  bytes_at segs m' a (upd_bytes bs (Z.to_nat k) p).
Proof.
  intros W m m' a bs k p HB MU HP Hk Hlen HOut.
  pose proof (bytes_at_bound segs m a bs HB) as [Ha0 Ha1].
  split; [exact Ha0|].
  split; [rewrite upd_bytes_length by lia; exact Ha1|].
  intros i Hi. rewrite upd_bytes_length in Hi by lia.
  rewrite upd_bytes_nth by lia.
  destruct (Nat.leb_spec (Z.to_nat k) i) as [H1|H1]; destruct (Nat.ltb_spec i (Z.to_nat k + length p)) as [H2|H2];
    cbn [andb].
  - destruct HP as (_ & _ & HPn).
    replace (a + Z.of_nat i) with (a + k + Z.of_nat (i - Z.to_nat k)) by lia.
    apply HPn. lia.
  - destruct HB as (_ & _ & HBn). unfold mrd. rewrite MU; [apply HBn; lia|].
    rewrite wa_unsigned by lia. apply HOut; lia.
  - destruct HB as (_ & _ & HBn). unfold mrd. rewrite MU; [apply HBn; lia|].
    rewrite wa_unsigned by lia. apply HOut; lia.
  - destruct HB as (_ & _ & HBn). unfold mrd. rewrite MU; [apply HBn; lia|].
    rewrite wa_unsigned by lia. apply HOut; lia.
Qed.

End Patch.

(** * 3. The spine step of the model branch (SegModel.r_key) *)

Lemma p7_r_key : forall (rc : rconf) (gi : nat) (nm line key val : list Z) (ln : Z),
  (exists ei : nat, strchr line EQ = Some ei /\ key = r_trim (firstn ei line) /\
                    val = r_unquote (r_trim (skipn (S ei) line))) ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model = 0 ->
  r_key rc (Some gi) nm ln line =
    match by_token (r_low val 0 24) with
    | None => (refuse rc ln F_badmodel [AS nm; AS val; AS known], Some gi, nm)
    | Some _ => (r_upd rc gi (rs_with_model (snprintf_s 24 F_s [AS (r_low val 0 24)])
                                            (snprintf_s 96 F_s [AS (rc_reading rc)])), Some gi, nm)
    end.
Proof.
  intros rc gi nm line key val ln (ei & Hei & Hk & Hv) Hrole Hmodel.
  subst key val.
  apply Z.eqb_neq in Hrole. apply Z.eqb_eq in Hmodel.
  unfold r_key. rewrite Hei. cbv iota zeta. rewrite Hrole, Hmodel. cbv iota. reflexivity.
Qed.

(** * 4. The fold into low[24] (R:254-256) *)

(** The bytes the loop stores before the NUL: the first min(cap - 1, |val|) bytes of val, folded. *)
Lemma p7_low_map : forall (v : list Z) (cap : nat), nulfree v -> r_low v 0 cap = map lower (firstn (cap - 1) v).
Proof. intros v cap H. exact (r_low_fold_go cap v 0%nat H). Qed.

Lemma p7_low_len : forall (v : list Z) (cap : nat), nulfree v ->
  length (r_low v 0 cap) = Nat.min (cap - 1) (length v).
Proof.
  intros v cap H. rewrite (p7_low_map v cap H), length_map, length_firstn. reflexivity.
Qed.

Lemma p7_low_nulfree : forall (v : list Z) (cap : nat), nulfree v -> nulfree (r_low v 0 cap).
Proof.
  intros v cap H. rewrite (p7_low_map v cap H). apply nulfree_map_lower. apply nulfree_firstn. exact H.
Qed.

Lemma p7_low_byte : forall (v : list Z) (cap : nat), nulfree v -> Forall (fun x => 0 <= x < 256) v ->
  Forall (fun x => 0 <= x < 256) (r_low v 0 cap).
Proof.
  intros v cap H HB. rewrite (p7_low_map v cap H).
  apply Forall_forall. intros y Hy. apply in_map_iff in Hy as (x & <- & Hx).
  assert (Hx2 : 0 <= x < 256).
  { rewrite Forall_forall in HB. apply HB.
    rewrite <- (firstn_skipn (cap - 1) v). apply in_or_app. left. exact Hx. }
  unfold lower. destruct ((65 <=? x) && (x <=? 90)) eqn:E; [|exact Hx2].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma p7_lower_range : forall x, 0 <= x < 256 -> 0 <= lower x < 256.
Proof.
  intros x Hx. unfold lower. destruct ((65 <=? x) && (x <=? 90)) eqn:E; [|exact Hx].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(** The byte the fold loop stores: `a3 = (b - 'A') <u 26`, `a0 = b + (a3 << 5)` (R:255, 0x150cc .. 0x150e4). *)
Lemma p7_fold_byte : forall x, 0 <= x < 256 ->
  x + Z.shiftl (Z.b2z ((x + -65) mod 18446744073709551616 <? 26)) 5 = lower x.
Proof.
  intros x Hx. unfold lower.
  destruct (Z.leb_spec 65 x) as [H1|H1]; destruct (Z.leb_spec x 90) as [H2|H2]; cbn [andb].
  - rewrite (Z.mod_small (x + -65)) by lia.
    rewrite (proj2 (Z.ltb_lt (x + -65) 26)) by lia. cbn [Z.b2z].
    change (Z.shiftl 1 5) with 32. lia.
  - rewrite (Z.mod_small (x + -65)) by lia.
    rewrite (proj2 (Z.ltb_ge (x + -65) 26)) by lia. cbn [Z.b2z].
    change (Z.shiftl 0 5) with 0. lia.
  - rewrite <- (Z.mod_add (x + -65) 1 18446744073709551616) by lia.
    rewrite (Z.mod_small (x + -65 + 1 * 18446744073709551616)) by lia.
    rewrite (proj2 (Z.ltb_ge (x + -65 + 1 * 18446744073709551616) 26)) by lia. cbn [Z.b2z].
    change (Z.shiftl 0 5) with 0. lia.
  - lia.
Qed.

(** A byte value as a 64-bit register word. *)
Lemma p7_byte_word : forall x, 0 <= x < 256 -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma p7_unsigned_byte : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(** snprintf(dst, 24, "%s", low) stores low itself (at most 23 bytes, NUL-free). *)
Lemma p7_snprintf_low : forall (v : list Z), nulfree v -> snprintf_s 24 F_s [AS (r_low v 0 24)] = r_low v 0 24.
Proof.
  intros v H. apply snprintf_s1; [apply p7_low_nulfree; exact H|].
  rewrite (p7_low_len v 24%nat H). lia.
Qed.

(** * 5. The join of the 11 catalogue tokens (R:258-263) *)

Definition p7_sep (ti : nat) : list Z := if (ti =? 0)%nat then [] else [124].
Definition p7_tok (ti : nat) : list Z := nth ti cat_toks [].
Definition p7_args (ti : nat) : list arg := [AS (p7_sep ti); AS (p7_tok ti)].
Definition p7_J (ti : nat) : list Z := known_go (firstn ti cat_toks) true 0 [].
Definition p7_kn (ti : nat) : Z := Z.of_nat (length (p7_J ti)).
Definition p7_kns : list Z := [0; 5; 11; 18; 30; 36; 42; 49; 56; 63; 70; 77].

Lemma p7_kn_nth : forall ti, (ti <= 11)%nat -> p7_kn ti = nth ti p7_kns 0.
Proof. intros ti H. do 12 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma p7_kn_bound : forall ti, (ti <= 11)%nat -> 0 <= p7_kn ti <= 77.
Proof.
  intros ti H.
  do 12 (destruct ti as [|ti]; [rewrite p7_kn_nth by lia; cbv [p7_kns nth]; lia|]).
  lia.
Qed.

Lemma p7_J_step : forall ti, (ti <= 10)%nat ->
  p7_J (S ti) = p7_J ti ++ snprintf_s (240 - p7_kn ti) F_ss (p7_args ti).
Proof. intros ti H. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma p7_r_step : forall ti, (ti <= 10)%nat ->
  snprintf_r F_ss (p7_args ti) = p7_kn (S ti) - p7_kn ti.
Proof. intros ti H. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma p7_J_11 : p7_J 11 = known.
Proof. vm_compute. reflexivity. Qed.

Lemma p7_J_nulfree : forall ti, (ti <= 11)%nat -> ~ In 0 (p7_J ti).
Proof.
  intros ti H.
  do 12 (destruct ti as [|ti];
         [intros C; vm_compute in C; repeat (destruct C as [C|C]; [discriminate C|]); exact C|]).
  lia.
Qed.

Lemma p7_J_byte : forall ti, (ti <= 11)%nat -> Forall (fun x => 0 <= x < 256) (p7_J ti).
Proof.
  intros ti H.
  do 12 (destruct ti as [|ti]; [apply p7_zbyte_forallb; vm_compute; reflexivity|]).
  lia.
Qed.

Lemma p7_sep_ok : forall ti, (ti <= 10)%nat ->
  Forall (fun x => 0 <= x < 256) (p7_sep ti) /\ ~ In 0 (p7_sep ti).
Proof.
  intros ti H. unfold p7_sep. destruct (ti =? 0)%nat.
  - split; [constructor | intros []].
  - split; [apply p7_zbyte_forallb; vm_compute; reflexivity|].
    intros C; vm_compute in C; repeat (destruct C as [C|C]; [discriminate C|]); exact C.
Qed.

Definition p7_tok_lens : list nat := [5; 5; 6; 11; 5; 5; 6; 6; 6; 6; 6]%nat.

Lemma p7_tok_len : forall ti, (ti <= 10)%nat -> length (p7_tok ti) = nth ti p7_tok_lens 0%nat.
Proof. intros ti H. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). lia. Qed.

Lemma p7_tok_ok : forall ti, (ti <= 10)%nat ->
  Forall (fun x => 0 <= x < 256) (p7_tok ti) /\ ~ In 0 (p7_tok ti) /\ (0 < length (p7_tok ti) <= 11)%nat.
Proof.
  intros ti H.
  do 11 (destruct ti as [|ti];
         [split; [apply p7_zbyte_forallb; vm_compute; reflexivity|];
          split; [intros C; vm_compute in C; repeat (destruct C as [C|C]; [discriminate C|]); exact C|];
          rewrite p7_tok_len by lia; cbv [p7_tok_lens nth]; lia|]).
  lia.
Qed.

(** The join's length (seg_spec.known_length restated). *)
Lemma p7_known_len : length known = 77%nat.
Proof. exact known_length. Qed.

(** The catalogue index of a hit is one of the 11 rows. *)
Lemma p7_row_go_lt : forall toks tk i j, row_go toks tk i = Some j -> (i <= j < i + length toks)%nat.
Proof.
  induction toks as [|k r IH]; intros tk i j H; [discriminate|].
  cbn [row_go length] in *.
  destruct ((length k =? length tk)%nat && leqb k tk).
  - injection H as <-. lia.
  - specialize (IH tk (S i) j H). lia.
Qed.

Lemma p7_by_token_lt : forall tok j, by_token tok = Some j -> (j < 11)%nat.
Proof.
  intros tok j H. unfold by_token, cat_row in H.
  pose proof (p7_row_go_lt cat_toks (cut_nul tok) 0%nat j H) as HB.
  assert (E : length cat_toks = 11%nat) by (vm_compute; reflexivity). lia.
Qed.

Lemma p7_skipn_nth : forall {A} (l : list A) i (dd : A), (i < length l)%nat ->
  skipn i l = nth i l dd :: skipn (S i) l.
Proof.
  intros A l. induction l as [|x l IH]; intros [|i] dd H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

(** The slack of a C string in a 24-byte buffer at an 8-aligned address: the next 8-byte boundary above
    the NUL is at or below the buffer's end. *)
Lemma p7_slack8 : forall A k, A mod 8 = 0 -> 0 <= k <= 23 -> (- (A + k + 1)) mod 8 <= 23 - k.
Proof. intros A k HA Hk. Z.div_mod_to_equations. lia. Qed.

(* The P7 miss path (image-free). *)

(** * 6. (P7 miss path) One pass of the join loop in the snprintf contract's terms *)

(** Pass ti writes sep ++ tok (it fits: kn + 12 < 240) and returns its length, the step of kn. *)
Lemma p7m_seg : forall ti, (ti <= 10)%nat ->
  p7_J (S ti) = p7_J ti ++ (p7_sep ti ++ p7_tok ti) /\
  Z.of_nat (length (p7_sep ti ++ p7_tok ti)) = p7_kn (S ti) - p7_kn ti.
Proof. intros ti H. do 11 (destruct ti as [|ti]; [split; vm_compute; reflexivity|]). lia. Qed.
(** (end of the P7 miss path block) *)
