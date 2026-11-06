(* omx-clap-core/fuzz_preset: P8 part D5 -- the largest piece of the writer chains, paid from the weight.

   PresetFlush.w_flush_ge loses Z.max 4096 (3 * maxpiece t p) bytes of the flush, and r_flush_ge loses
   2 * rmaxpiece t p * (log2 - 1). This file bounds both pieces by lmax t, the longest decoded string, member name or
   number text of t, and pays lmax t from PjWeight.wsum, which charges w_len per byte of such a piece of length at
   least w_lmin.

   WHAT IS PROVED.
   - maxpiece_lmax, rmaxpiece_lmax: every piece is at most max 6 (lmax t). The writer puts a string as runs of raw
     decoded bytes between its escapes, and each escape (at most 6 bytes, \u00XX) as its own piece
     (WriterSpec.spieces); rendered () puts a string one character at a time (PresetReqAt.tx_str, at most 6 each).
     The other pieces are at most 6: a literal (5), punctuation (1), a separator (2), an indentation step (2), a
     newline (1). So the factor is 1, not 6. Both constants are reached (maxpiece_lmax_tight, rmaxpiece_lmax_tight):
     JStr [1] has lmax 1 and a 6-byte piece; a 7-digit number has lmax 7 and a 7-byte piece.
   - wsum_lmax: with all weights non-negative, w_len * lmax t <= wsum W t once lmax t >= w_lmin. It uses kwt only
     through 0 <= kwt W n, which holds for any kwt that is w_k64 W or 0.
   - lmax_copy_set, nc9_copy_set, nk65_copy_set: the rewrite's pj_set ("modifiedAt": "2026-10-25T00:00:00Z") adds
     at most its key and value to lmax, and at most one to nc9 and to nk65 (the object may reach 9 or 65 members).
   - wlen_copy_set: the copy's text is at most 40 bytes longer than the doc's. Pretty, an appended member costs
     its comma, its line (3), the quoted key (12), ": " (2) and the quoted value (22): 40, reached by the empty
     object (wlen_copy_set_tight); a replaced value costs at most 22 - 1. The proof is PackTraceR.crt_wlen's.

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
  WriterSpec WriterValue PjWriteHyp SlotSizes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PjGrammar PjRoundTrip PresetReqAt PresetFlush PjWeight.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ lmax *)

(* the longest string, member name or number text of t *)
Fixpoint lmax (t : jv) : nat :=
  match t with
  | JNum txt _ => length txt
  | JStr s => length s
  | JArr items => list_max (map lmax items)
  | JObj ms => list_max (map (fun '(k, u) => Nat.max (length k) (lmax u)) ms)
  | _ => 0%nat
  end.

Lemma pc_lmax_arr : forall items, lmax (JArr items) = list_max (map lmax items).
Proof. reflexivity. Qed.

Lemma pc_lmax_obj : forall ms, lmax (JObj ms) = list_max (map (fun '(k, u) => Nat.max (length k) (lmax u)) ms).
Proof. reflexivity. Qed.

Lemma pc_le_max : forall l x, In x l -> (x <= list_max l)%nat.
Proof.
  induction l as [|a l IH]; intros x H; [destruct H|].
  change (list_max (a :: l)) with (Nat.max a (list_max l)).
  destruct H as [<- | H]; [lia|]. specialize (IH x H). lia.
Qed.

Lemma pc_lmax_cons : forall (A : Type) (f : A -> nat) a l, list_max (map f (a :: l)) = Nat.max (f a) (list_max (map f l)).
Proof. reflexivity. Qed.

Lemma pc_fr_cons : forall (A : Type) (f : A -> Z) a l,
  fold_right Z.add 0 (map f (a :: l)) = f a + fold_right Z.add 0 (map f l).
Proof. reflexivity. Qed.

(* every string, name and number text of t is at most lmax t long *)
Lemma tlen_lmax : forall t, tlen (lmax t) t.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  - exact I.
  - exact I.
  - exact I.
  - cbn [tlen lmax]. lia.
  - cbn [tlen lmax]. lia.
  - apply tlen_arr. rewrite Forall_forall in IH |- *. intros u Hu.
    apply (tlen_mono u (lmax u)); [|exact (IH u Hu)].
    rewrite pc_lmax_arr. apply pc_le_max. apply in_map. exact Hu.
  - apply tlen_obj. rewrite Forall_forall in IH |- *. intros [k u] Hm. cbn [fst snd] in *.
    assert (Hl : (Nat.max (length k) (lmax u) <= lmax (JObj ms))%nat).
    { rewrite pc_lmax_obj. apply pc_le_max.
      exact (in_map (fun '(k0, u0) => Nat.max (length k0) (lmax u0)) ms (k, u) Hm). }
    split; [lia|]. apply (tlen_mono u (lmax u)); [lia | exact (IH (k, u) Hm)].
Qed.

(* ================================================================ the largest pieces *)

Lemma pc_maxpiece_tlen : forall t p M, (6 <= M)%nat -> tlen M t -> maxpiece t p <= Z.of_nat M.
Proof.
  intros t p M H6 HM.
  assert (HF : Forall (fun b => (length b <= M)%nat) (wdpieces t p)).
  { unfold wdpieces. apply Forall_app. split; [apply wv_le; assumption|].
    destruct p; [constructor; [cbn [length]; lia | constructor] | constructor]. }
  unfold maxpiece. apply fmax_le; [lia|].
  unfold piece_lens. apply Forall_map. eapply Forall_impl; [|exact HF]. intros b Hb. cbv beta in *. lia.
Qed.

Lemma pc_rmaxpiece_tlen : forall t p M, (6 <= M)%nat -> tlen M t -> rmaxpiece t p <= Z.of_nat M.
Proof.
  intros t p M H6 HM. unfold rmaxpiece, rpieces. apply fmax_le; [lia|].
  apply Forall_app. split; [apply txv_le; assumption|].
  destruct p; [constructor; [lia | constructor] | constructor].
Qed.

Lemma pc_tlen6 : forall t, tlen (Nat.max 6 (lmax t)) t.
Proof. intros t. apply (tlen_mono t (lmax t)); [apply Nat.le_max_r | apply tlen_lmax]. Qed.

Theorem maxpiece_lmax : forall t p, maxpiece t p <= Z.max 6 (Z.of_nat (lmax t)).
Proof.
  intros t p. pose proof (pc_maxpiece_tlen t p (Nat.max 6 (lmax t)) (Nat.le_max_l _ _) (pc_tlen6 t)). lia.
Qed.

Theorem rmaxpiece_lmax : forall t p, rmaxpiece t p <= Z.max 6 (Z.of_nat (lmax t)).
Proof.
  intros t p. pose proof (pc_rmaxpiece_tlen t p (Nat.max 6 (lmax t)) (Nat.le_max_l _ _) (pc_tlen6 t)). lia.
Qed.

(* both constants are reached: a control character's 6-byte escape at lmax 1, a number's text at lmax 7 *)
Example maxpiece_lmax_tight :
  lmax (JStr [1]) = 1%nat /\ maxpiece (JStr [1]) false = 6 /\
  lmax (JNum (repeat 49 7) 0) = 7%nat /\ maxpiece (JNum (repeat 49 7) 0) false = 7.
Proof. vm_compute. repeat constructor. Qed.

Example rmaxpiece_lmax_tight :
  rmaxpiece (JStr [1]) false = 6 /\ rmaxpiece (JNum (repeat 49 7) 0) false = 7.
Proof. vm_compute. repeat constructor. Qed.

(* ================================================================ wsum pays lmax *)

(* the w_len share of a piece of length k *)
Definition lwt (W : nweights) (k : nat) : Z := if Nat.leb (w_lmin W) k then w_len W * Z.of_nat k else 0.

(* all the weights are non-negative *)
Definition wnn (W : nweights) : Prop :=
  0 <= w_c18 W /\ 0 <= w_c9 W /\ 0 <= w_k64 W /\ 0 <= w_str W /\ 0 <= w_num W /\ 0 <= w_len W.

Lemma pc_lwt0 : forall W, lwt W 0 = 0.
Proof. intros W. unfold lwt. destruct (Nat.leb (w_lmin W) 0); cbn [Z.of_nat]; lia. Qed.

Lemma pc_lwt_nonneg : forall W k, 0 <= w_len W -> 0 <= lwt W k.
Proof.
  intros W k H. unfold lwt.
  destruct (Nat.leb (w_lmin W) k); cbv beta iota; [apply Z.mul_nonneg_nonneg; lia | lia].
Qed.

Lemma pc_lwt_max : forall W a b, 0 <= w_len W -> lwt W (Nat.max a b) <= lwt W a + lwt W b.
Proof.
  intros W a b H. pose proof (pc_lwt_nonneg W a H). pose proof (pc_lwt_nonneg W b H).
  destruct (Nat.max_spec a b) as [[_ ->] | [_ ->]]; lia.
Qed.

Lemma pc_swt : forall W k, wnn W -> 0 <= swt W k /\ lwt W k <= swt W k.
Proof.
  intros W k (A & B & C & D & E & F). unfold swt, lwt.
  assert (0 <= w_len W * Z.of_nat k) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (Nat.leb 72 k); destruct (Nat.leb (w_lmin W) k); cbv beta iota; lia.
Qed.

Lemma pc_nwt : forall W k, wnn W -> 0 <= nwt W k /\ lwt W k <= nwt W k.
Proof.
  intros W k (A & B & C & D & E & F). unfold nwt, lwt.
  assert (0 <= w_len W * Z.of_nat k) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (Nat.leb 432 k); destruct (Nat.leb (w_lmin W) k); cbv beta iota; lia.
Qed.

Lemma pc_cwt : forall W n, wnn W -> 0 <= cwt W n.
Proof.
  intros W n (A & B & _). unfold cwt.
  repeat match goal with |- context [if ?b then _ else _] => destruct b; cbv beta iota end; lia.
Qed.

(* the only fact of kwt used: it is w_k64 W or 0 *)
Lemma pc_kwt : forall W n, wnn W -> 0 <= kwt W n.
Proof.
  intros W n (_ & _ & C & _). unfold kwt.
  repeat match goal with |- context [if ?b then _ else _] => destruct b; cbv beta iota end; lia.
Qed.

Lemma pc_wsum_arr : forall W items, wsum W (JArr items) = cwt W (length items) + fold_right Z.add 0 (map (wsum W) items).
Proof. reflexivity. Qed.

Lemma pc_wsum_obj : forall W ms, wsum W (JObj ms) = cwt W (length ms) + kwt W (length ms) +
  fold_right Z.add 0 (map (fun m => swt W (length (fst m)) + wsum W (snd m)) ms).
Proof. reflexivity. Qed.

Lemma pc_sum_arr : forall W items, wnn W ->
  Forall (fun u => 0 <= wsum W u /\ lwt W (lmax u) <= wsum W u) items ->
  0 <= fold_right Z.add 0 (map (wsum W) items) /\
  lwt W (list_max (map lmax items)) <= fold_right Z.add 0 (map (wsum W) items).
Proof.
  intros W items HW H. pose proof HW as (_ & _ & _ & _ & _ & F).
  induction H as [|u l [H1 H2] _ [IH1 IH2]].
  - cbn [map fold_right list_max]. rewrite pc_lwt0. lia.
  - rewrite pc_lmax_cons, pc_fr_cons. pose proof (pc_lwt_max W (lmax u) (list_max (map lmax l)) F). lia.
Qed.

Lemma pc_sum_obj : forall W (ms : list (list Z * jv)), wnn W ->
  Forall (fun m => 0 <= wsum W (snd m) /\ lwt W (lmax (snd m)) <= wsum W (snd m)) ms ->
  0 <= fold_right Z.add 0 (map (fun m => swt W (length (fst m)) + wsum W (snd m)) ms) /\
  lwt W (list_max (map (fun '(k, u) => Nat.max (length k) (lmax u)) ms)) <=
    fold_right Z.add 0 (map (fun m => swt W (length (fst m)) + wsum W (snd m)) ms).
Proof.
  intros W ms HW H. pose proof HW as (_ & _ & _ & _ & _ & F).
  induction H as [|m l [H1 H2] _ [IH1 IH2]].
  - cbn [map fold_right list_max]. rewrite pc_lwt0. lia.
  - destruct m as [k u]. cbn [fst snd] in H1, H2.
    rewrite pc_lmax_cons, pc_fr_cons. cbv beta iota. cbn [fst snd].
    match goal with |- context [lwt W (Nat.max (Nat.max (length k) (lmax u)) ?R)] =>
      pose proof (pc_lwt_max W (Nat.max (length k) (lmax u)) R F) end.
    pose proof (pc_lwt_max W (length k) (lmax u) F). pose proof (pc_swt W (length k) HW). lia.
Qed.

Lemma pc_wsum : forall W t, wnn W -> 0 <= wsum W t /\ lwt W (lmax t) <= wsum W t.
Proof.
  intros W t HW.
  induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  - cbn [wsum lmax]. rewrite pc_lwt0. lia.
  - cbn [wsum lmax]. rewrite pc_lwt0. lia.
  - cbn [wsum lmax]. rewrite pc_lwt0. lia.
  - cbn [wsum lmax]. exact (pc_nwt W (length txt) HW).
  - cbn [wsum lmax]. exact (pc_swt W (length s) HW).
  - rewrite pc_wsum_arr, pc_lmax_arr. pose proof (pc_cwt W (length items) HW).
    destruct (pc_sum_arr W items HW IH). lia.
  - rewrite pc_wsum_obj, pc_lmax_obj. pose proof (pc_cwt W (length ms) HW). pose proof (pc_kwt W (length ms) HW).
    destruct (pc_sum_obj W ms HW IH). lia.
Qed.

Theorem wsum_lmax : forall W t, 0 <= w_c18 W -> 0 <= w_c9 W -> 0 <= w_k64 W -> 0 <= w_str W -> 0 <= w_num W ->
  0 <= w_len W -> (w_lmin W <= lmax t)%nat -> w_len W * Z.of_nat (lmax t) <= wsum W t.
Proof.
  intros W t H1 H2 H3 H4 H5 H6 Hm.
  destruct (pc_wsum W t (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6)))))) as [_ H].
  unfold lwt in H. rewrite (proj2 (Nat.leb_le _ _) Hm) in H. exact H.
Qed.

(* ================================================================ the rewrite's copy *)

Theorem lmax_copy_set : forall ms,
  (lmax (copy_set ms) <= Nat.max (lmax (JObj ms)) (Nat.max (length MOD_KEY) (length MOD_VAL)))%nat.
Proof.
  intros ms. unfold copy_set. rewrite pc_lmax_obj.
  apply list_max_le. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as ([k u] & <- & Hm).
  cbv beta iota.
  destruct (set_model_in ms MOD_KEY (JStr MOD_VAL) (k, u) Hm) as [Hin | Heq].
  - assert (H : (Nat.max (length k) (lmax u) <= lmax (JObj ms))%nat).
    { rewrite pc_lmax_obj. apply pc_le_max.
      exact (in_map (fun '(k0, u0) => Nat.max (length k0) (lmax u0)) ms (k, u) Hin). }
    lia.
  - injection Heq as -> ->. cbn [lmax]. lia.
Qed.

(* the per-member sum of f over an object's values *)
Definition msumf (f : jv -> nat) (L : list (list Z * jv)) : nat := list_sum (map (fun '(_, u) => f u) L).

Lemma pc_nc9_obj : forall L, nc9 (JObj L) = ((if Nat.leb 9 (length L) then 1 else 0) + msumf nc9 L)%nat.
Proof. reflexivity. Qed.

Lemma pc_nk65_obj : forall L, nk65 (JObj L) = ((if Nat.leb 65 (length L) then 1 else 0) + msumf nk65 L)%nat.
Proof. reflexivity. Qed.

(* pj_set of a value f does not count: the sum does not grow *)
Lemma pc_set_sum : forall (f : jv -> nat) ms kn tv, f tv = 0%nat ->
  (msumf f (pj_set_model ms kn tv) <= msumf f ms)%nat.
Proof.
  intros f ms kn tv H0. unfold msumf. induction ms as [|[k v] r IH]; cbn [pj_set_model].
  - rewrite map_cons, lsum_cons. cbv beta iota. cbn [map list_sum fold_right]. lia.
  - destruct (list_eq_dec Z.eq_dec k kn) as [E | E]; cbv beta iota; rewrite !map_cons, !lsum_cons; cbv beta iota;
      lia.
Qed.

Theorem nc9_copy_set : forall ms, (nc9 (copy_set ms) <= nc9 (JObj ms) + 1)%nat.
Proof.
  intros ms. unfold copy_set. rewrite !pc_nc9_obj.
  pose proof (pc_set_sum nc9 ms MOD_KEY (JStr MOD_VAL) eq_refl) as H.
  destruct (Nat.leb 9 (length (pj_set_model ms MOD_KEY (JStr MOD_VAL)))); destruct (Nat.leb 9 (length ms));
    cbv beta iota; lia.
Qed.

Theorem nk65_copy_set : forall ms, (nk65 (copy_set ms) <= nk65 (JObj ms) + 1)%nat.
Proof.
  intros ms. unfold copy_set. rewrite !pc_nk65_obj.
  pose proof (pc_set_sum nk65 ms MOD_KEY (JStr MOD_VAL) eq_refl) as H.
  destruct (Nat.leb 65 (length (pj_set_model ms MOD_KEY (JStr MOD_VAL)))); destruct (Nat.leb 65 (length ms));
    cbv beta iota; lia.
Qed.

(* ================================================================ the copy's text

   Adapted from lib/Prog/PackTraceR.v:680-704 (stamp_len, wgo_set, crt_wlen). There crt_tree (JObj ms) is
   JObj (pj_set_model ms MOD_AT (JStr STAMP)) (lib/Prog/check_round_trip_c.v:25), MOD_AT and STAMP byte for byte
   PresetReqAt's MOD_KEY and MOD_VAL; here the tree is copy_set ms. PackTraceR is not imported: it brings in the
   plain program proofs. *)

Lemma pc_modval_len : forall p d, length (concat (wvpieces (JStr MOD_VAL) p d)) = 22%nat.
Proof. intros p d. vm_compute. reflexivity. Qed.

Lemma pc_wgo_set : forall p ms i,
  Z.of_nat (length (concat (wgo_obj p 0 i (pj_set_model ms MOD_KEY (JStr MOD_VAL))))) <=
  Z.of_nat (length (concat (wgo_obj p 0 i ms))) + 40.
Proof.
  intros p. induction ms as [|[k v] r IH]; intros i; cbn [pj_set_model].
  - destruct p, i; apply Z.leb_le; vm_compute; reflexivity.
  - destruct (list_eq_dec Z.eq_dec k MOD_KEY) as [E|E]; cbn [wgo_obj]; rewrite !concat_app, !length_app.
    + rewrite pc_modval_len. lia.
    + specialize (IH (S i)). lia.
Qed.

Theorem wlen_copy_set : forall ms p, wlen (copy_set ms) p <= wlen (JObj ms) p + 40.
Proof.
  intros ms p. unfold copy_set. destruct ms as [|[k0 v0] ms0].
  - destruct p; apply Z.leb_le; vm_compute; reflexivity.
  - assert (Hne : exists m' ms', pj_set_model ((k0, v0) :: ms0) MOD_KEY (JStr MOD_VAL) = m' :: ms').
    { cbn [pj_set_model]. destruct (list_eq_dec Z.eq_dec k0 MOD_KEY); eexists; eexists; reflexivity. }
    destruct Hne as (m' & ms' & Ens). pose proof (pc_wgo_set p ((k0, v0) :: ms0) 0) as W.
    unfold wlen, wdoc, wdpieces. rewrite !concat_app, !obj_text. rewrite Ens in W |- *.
    cbn [length]. rewrite !length_app. cbn [length]. lia.
Qed.

(* 40 is reached: {} grows to {"modifiedAt": "2026-10-25T00:00:00Z"} *)
Example wlen_copy_set_tight : wlen (copy_set []) true = wlen (JObj []) true + 40.
Proof. vm_compute. reflexivity. Qed.
