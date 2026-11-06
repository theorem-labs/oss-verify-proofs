(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput, both builds: the turn in the spine's terms and the
   model facts the slot side of the walk needs (build-independent: Spec/SegModel.v and Prog/seg_spec.v only).
   - l02_step: seg_spec.seg_turn_step with the text s and the label byte lb explicit (what the inner walks,
     Prog/Seg/L02W.v and U/Prog/Seg/L02W.v, compute);
   - L02_model: the turn's data and counter bounds the inner walks take.
   Model lemmas of a segment walk. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** The turn: seg_spec.seg_turn_step with the text s and the label byte lb explicit. *)
Definition l02_step (s : list Z) (lb : Z) (last : bool) (st : rconf * mconf * bool) : rconf * mconf * bool :=
  let '(c, mc, ret) := st in
  if last then
    let m1 := m_cross (m_file mc s None) in
    let (c1, n) := r_parse c s in
    (c1, m1, ret && (n =? Z.of_nat (length (mc_seg m1))))
  else
    let l := label_of lb in
    let m1 := m_file mc s l in
    let (c1, n) := r_parse_file c s l in
    (c1, m1, ret && (n =? Z.of_nat (length (mc_seg m1)))).

(** The turn's data: the text is bytes 1 .. 255 (fuzz_str cut it at its first NUL) and at most 65535 of them (a u16
    length), lb a byte, and the counters far enough from their bounds for m_file, the reader and m_cross's m_refuse
    calls (at most 65535 lines a call, at most 32 refusals in m_cross). *)
Definition L02_model (s : list Z) (lb : Z) (rc : rconf) (mc : mconf) : Prop :=
  Forall (fun x => 0 < x < 256) s /\ (length s <= 65535)%nat /\ 0 <= lb < 256 /\
  rc_gen rc + 1 < 2 ^ 32 /\ rc_refused rc + 2 ^ 17 < 2 ^ 32 /\ rc_overflow rc + 2 ^ 17 < 2 ^ 32 /\
  mc_gen mc + 1 < 2 ^ 31 /\ mc_refused mc + 2 ^ 18 < 2 ^ 32 /\ mc_overflow mc + 2 ^ 17 < 2 ^ 32.

(** ** The model facts of the turn (build-independent) *)

(** *** The cursor: one file record read (lb, the u16 length, fuzz_take's bytes) and the record it decodes. *)
Definition l02m_next (l : list Z) : list Z :=
  snd (fuzz_take (snd (fuzz_u16 (snd (fuzz_u8 l)))) (fst (fuzz_u16 (snd (fuzz_u8 l))))).
Definition l02m_rec (l : list Z) : file :=
  File (fst (fuzz_u8 l))
       (fuzz_str (fst (fuzz_take (snd (fuzz_u16 (snd (fuzz_u8 l)))) (fst (fuzz_u16 (snd (fuzz_u8 l))))))).

Lemma l02m_skip_1 k l : seg_skip (S k) l = seg_skip k (l02m_next l).
Proof.
  unfold l02m_next. cbn [seg_skip].
  destruct (fuzz_u8 l) as [a i1]. cbn [fst snd].
  destruct (fuzz_u16 i1) as [len i2]. cbn [fst snd].
  destruct (fuzz_take i2 len) as [x i3]. reflexivity.
Qed.

Lemma l02m_skip_S k : forall l, seg_skip (S k) l = l02m_next (seg_skip k l).
Proof.
  induction k as [|k IH]; intros l.
  - rewrite (l02m_skip_1 0 l). reflexivity.
  - rewrite (l02m_skip_1 (S k) l), (IH (l02m_next l)), <- (l02m_skip_1 k l). reflexivity.
Qed.

Lemma l02m_dec_S k l : dec_files (S k) l = l02m_rec l :: dec_files k (l02m_next l).
Proof.
  unfold l02m_rec, l02m_next. cbn [dec_files].
  destruct (fuzz_u8 l) as [a i1]. cbn [fst snd].
  destruct (fuzz_u16 i1) as [len i2]. cbn [fst snd].
  destruct (fuzz_take i2 len) as [x i3]. reflexivity.
Qed.

Lemma l02m_dec_len k : forall l, length (dec_files k l) = k.
Proof.
  induction k as [|k IH]; intros l; [reflexivity|]. rewrite l02m_dec_S. cbn [length]. rewrite IH. reflexivity.
Qed.

Lemma l02m_dec_nth f : forall k l, (f < k)%nat -> nth f (dec_files k l) (File 0 []) = l02m_rec (seg_skip f l).
Proof.
  induction f as [|f IH]; intros k l Hf; destruct k as [|k]; try lia; rewrite l02m_dec_S.
  - reflexivity.
  - cbn [nth]. rewrite l02m_skip_1. apply IH. lia.
Qed.

(** decode reads its files from seg_hdr: seg_files is dec_files of 1 + b2 mod 4 records from there. *)
Lemma l02m_files inp :
  seg_files inp =
  dec_files (Z.to_nat (1 + fst (fuzz_u8 (snd (fuzz_u8 (snd (fuzz_u8 (seg_in inp)))))) mod 4)) (seg_hdr inp).
Proof.
  unfold seg_files, seg_pay, decode, seg_hdr.
  destruct (fuzz_u8 (seg_in inp)) as [b0 i1]. cbn [fst snd].
  destruct (fuzz_u8 i1) as [fl i2]. cbn [fst snd].
  destruct (fuzz_u8 i2) as [b2 i3]. reflexivity.
Qed.

Lemma l02m_nfiles_eq inp :
  seg_nfiles inp = 1 + fst (fuzz_u8 (snd (fuzz_u8 (snd (fuzz_u8 (seg_in inp)))))) mod 4.
Proof.
  unfold seg_nfiles. rewrite l02m_files, l02m_dec_len.
  pose proof (Z.mod_pos_bound (fst (fuzz_u8 (snd (fuzz_u8 (snd (fuzz_u8 (seg_in inp))))))) 4 ltac:(lia)).
  apply Z2Nat.id. lia.
Qed.

Lemma l02m_nfiles : forall inp, 1 <= seg_nfiles inp <= 4.
Proof.
  intros inp. rewrite l02m_nfiles_eq.
  pose proof (Z.mod_pos_bound (fst (fuzz_u8 (snd (fuzz_u8 (snd (fuzz_u8 (seg_in inp))))))) 4 ltac:(lia)). lia.
Qed.

Lemma l02m_file_in inp f : Z.of_nat f < seg_nfiles inp -> seg_file inp f = l02m_rec (seg_cur inp f).
Proof.
  intros Hf. unfold seg_file, seg_cur. unfold seg_nfiles in Hf. rewrite l02m_files in *.
  rewrite l02m_dec_len in Hf. apply l02m_dec_nth. lia.
Qed.

Lemma l02m_file_out inp f : ~ Z.of_nat f < seg_nfiles inp -> seg_file inp f = File 0 [].
Proof. intros Hf. unfold seg_file. apply nth_overflow. unfold seg_nfiles in Hf. lia. Qed.

(** Turn f's text and label byte, for f < nfiles. *)
Lemma l02m_txt_in inp f : Z.of_nat f < seg_nfiles inp ->
  seg_txt inp f = cut_nul (fst (fuzz_take (seg_turn_tail inp f) (seg_turn_len inp f))) /\
  seg_lb inp f = fst (fuzz_u8 (seg_cur inp f)).
Proof. intros Hf. unfold seg_txt, seg_lb. rewrite (l02m_file_in inp f Hf). split; reflexivity. Qed.

(** *** The cursor and the turn's tail are suffixes of the input. *)
Lemma l02m_u8_sfx l : snd (fuzz_u8 l) = skipn 1 l.
Proof. destruct l; reflexivity. Qed.
Lemma l02m_u16_sfx l : snd (fuzz_u16 l) = skipn 2 l.
Proof. unfold fuzz_u16. destruct l as [|a [|b r]]; reflexivity. Qed.
Lemma l02m_take_fst t w : fst (fuzz_take t w) = firstn (Nat.min (Z.to_nat w) (length t)) t.
Proof. reflexivity. Qed.
Lemma l02m_take_snd t w : snd (fuzz_take t w) = skipn (Nat.min (Z.to_nat w) (length t)) t.
Proof. reflexivity. Qed.
Lemma l02m_take_len t w :
  length (fst (fuzz_take t w)) = Nat.min (Z.to_nat w) (length t) /\
  length (snd (fuzz_take t w)) = (length t - Nat.min (Z.to_nat w) (length t))%nat.
Proof. rewrite l02m_take_fst, l02m_take_snd, length_firstn, length_skipn. split; [lia | reflexivity]. Qed.

Lemma l02m_next_sfx l : exists j, l02m_next l = skipn j l.
Proof.
  unfold l02m_next. rewrite l02m_take_snd, l02m_u16_sfx, l02m_u8_sfx, !skipn_skipn. eexists. reflexivity.
Qed.

Lemma l02m_skip_sfx k : forall l, exists j, seg_skip k l = skipn j l.
Proof.
  induction k as [|k IH]; intros l; [exists 0%nat; reflexivity|].
  rewrite l02m_skip_1. destruct (l02m_next_sfx l) as [i Hi]. destruct (IH (l02m_next l)) as [j Hj].
  rewrite Hj, Hi, skipn_skipn. eexists. reflexivity.
Qed.

Lemma l02m_cur_sfx inp f : exists j, seg_cur inp f = skipn j (seg_in inp).
Proof.
  unfold seg_cur, seg_hdr. destruct (l02m_skip_sfx f (snd (fuzz_u8 (snd (fuzz_u8 (snd (fuzz_u8 (seg_in inp))))))))
    as [j Hj].
  rewrite Hj, !l02m_u8_sfx, !skipn_skipn. eexists. reflexivity.
Qed.

Lemma l02m_tail_sfx inp f : exists j, seg_turn_tail inp f = skipn j (seg_in inp).
Proof.
  unfold seg_turn_tail. destruct (l02m_cur_sfx inp f) as [j Hj].
  rewrite l02m_u16_sfx, l02m_u8_sfx, Hj, !skipn_skipn. eexists. reflexivity.
Qed.

Lemma l02m_in_len inp : length (seg_in inp) = length inp.
Proof. unfold seg_in, zs. apply length_map. Qed.

Lemma l02m_in_ok inp : Forall byte_ok (seg_in inp).
Proof.
  unfold seg_in, zs. apply Forall_map, Forall_forall. intros b _. unfold byte_ok.
  pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma l02m_cut_nul_pre l : cut_nul l = firstn (length (cut_nul l)) l.
Proof.
  induction l as [|a l IH]; [reflexivity|]. cbn [cut_nul]. destruct (a =? 0); [reflexivity|].
  cbn [length firstn]. f_equal. exact IH.
Qed.

Lemma l02m_skipn_len {A} (l : list A) j : skipn (length l - length (skipn j l)) l = skipn j l.
Proof.
  rewrite length_skipn. destruct (Nat.le_gt_cases j (length l)).
  - f_equal. lia.
  - rewrite skipn_all2 by lia. symmetry. apply skipn_all2. lia.
Qed.

(** zb undoes zs. *)
Lemma l02m_zb_zs (l : list byte) : zb (zs l) = l.
Proof.
  unfold zb, zs. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma l02m_zb_firstn k (l : list byte) : zb (firstn k (zs l)) = firstn k l.
Proof. unfold zs. rewrite firstn_map. exact (l02m_zb_zs (firstn k l)). Qed.

(** The tail is the input's bytes from (length inp - its length). *)
Lemma l02m_tail_zs inp f :
  seg_turn_tail inp f = zs (skipn (length inp - length (seg_turn_tail inp f)) inp).
Proof.
  destruct (l02m_tail_sfx inp f) as [j Hj].
  pose proof (l02m_skipn_len (seg_in inp) j) as E. rewrite <- Hj, l02m_in_len in E.
  unfold zs. rewrite <- skipn_map. exact (eq_sym E).
Qed.

Lemma l02m_text_gen (T : list byte) m :
  zb (cut_nul (firstn m (zs T))) = firstn (length (cut_nul (firstn m (zs T)))) T.
Proof.
  pose proof (cut_nul_len (firstn m (zs T))) as H. rewrite length_firstn in H.
  rewrite l02m_cut_nul_pre at 1. rewrite firstn_firstn, (Nat.min_l _ m) by lia. apply l02m_zb_firstn.
Qed.

(** *** Every turn's data: the text NUL-free and at most 65535 bytes, the label a byte. *)
Lemma l02m_turn_ok inp f :
  nulfree (seg_txt inp f) /\ Z.of_nat (length (seg_txt inp f)) <= 65535 /\ 0 <= seg_lb inp f < 256.
Proof.
  change (file_ok (seg_file inp f)). unfold seg_file, seg_files, seg_pay.
  destruct (Nat.lt_ge_cases f (length (p_files (decode (seg_in inp))))) as [H|H].
  - pose proof (proj1 (decode_ok (seg_in inp) (l02m_in_ok inp))) as HF. rewrite Forall_forall in HF.
    apply HF, nth_In, H.
  - rewrite nth_overflow by exact H. unfold file_ok; cbn [f_text f_lb length Z.of_nat].
    split; [apply nulfree_nil | lia].
Qed.

Lemma l02m_txt_le inp f :
  (length (seg_txt inp f) <= length (fst (fuzz_take (seg_turn_tail inp f) (seg_turn_len inp f))))%nat.
Proof.
  destruct (Z_lt_dec (Z.of_nat f) (seg_nfiles inp)) as [Hf|Hf].
  - rewrite (proj1 (l02m_txt_in inp f Hf)). apply cut_nul_len.
  - unfold seg_txt. rewrite (l02m_file_out inp f Hf). cbn [f_text length]. lia.
Qed.

Lemma l02m_txt_ok inp f : Z.of_nat f < seg_nfiles inp -> Forall (fun x => 0 < x < 256) (seg_txt inp f).
Proof.
  intros Hf. rewrite (proj1 (l02m_txt_in inp f Hf)), l02m_take_fst.
  generalize (Nat.min (Z.to_nat (seg_turn_len inp f)) (length (seg_turn_tail inp f))) as m. intros m.
  destruct (l02m_tail_sfx inp f) as [j Hj]. rewrite Hj.
  assert (H : Forall byte_ok (cut_nul (firstn m (skipn j (seg_in inp))))).
  { rewrite l02m_cut_nul_pre. apply Forall_firstn', Forall_firstn', Forall_skipn', l02m_in_ok. }
  pose proof (cut_nul_nulfree (firstn m (skipn j (seg_in inp)))) as Hn.
  rewrite Forall_forall in H |- *. intros x Hx. specialize (H x Hx). unfold byte_ok in H.
  destruct (Z.eq_dec x 0) as [E|E]; [subst x; exfalso; exact (Hn Hx) | lia].
Qed.

(** *** The counters: m_file's (as Prog/m_file_c.v's m_file_gen, m_file_refused, m_file_overflow, restated here so
    that this file stays build-independent) and the drop-in turns' (conf_rel and the bounds). *)
Lemma l02m_header_cnt m l n :
  mc_gen (fst (m_header m l n)) = mc_gen m /\
  mc_refused m <= mc_refused (fst (m_header m l n)) <= mc_refused m + 1 /\
  mc_overflow m <= mc_overflow (fst (m_header m l n)) <= mc_overflow m + 1.
Proof.
  unfold m_header. cbv zeta. destruct (memchr l RBR) as [ci|]; [|cbn; lia].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [m_find ?a ?b] => destruct (m_find a b)
         end; cbn; lia.
Qed.

Lemma l02m_key_cnt m g l n :
  mc_gen (m_key m g l n) = mc_gen m /\
  mc_refused m <= mc_refused (m_key m g l n) <= mc_refused m + 1 /\
  mc_overflow (m_key m g l n) = mc_overflow m.
Proof.
  unfold m_key. cbv zeta. destruct (memchr l EQ); [|cbn; lia]. destruct g; [|cbn; lia].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         | |- context [h_role_word ?a] => destruct (h_role_word a)
         | |- context [cat_row ?a] => destruct (cat_row a)
         end; cbn; lia.
Qed.

Lemma l02m_line_cnt st n l :
  mc_gen (fst (m_line st n l)) = mc_gen (fst st) /\
  mc_refused (fst st) <= mc_refused (fst (m_line st n l)) <= mc_refused (fst st) + 1 /\
  mc_overflow (fst st) <= mc_overflow (fst (m_line st n l)) <= mc_overflow (fst st) + 1.
Proof.
  destruct st as [m cur]. unfold m_line. destruct (512 <=? length l)%nat; [cbn; lia|].
  destruct (h_strip (h_cut_comment l)) as [|b s]; [cbn; lia|].
  destruct (b =? LBR); cbn [fst]; [apply l02m_header_cnt|].
  pose proof (l02m_key_cnt m cur (b :: s) n) as H. lia.
Qed.

Lemma l02m_lines_cnt ls : forall st n,
  mc_gen (fst (m_lines st n ls)) = mc_gen (fst st) /\
  mc_refused (fst st) <= mc_refused (fst (m_lines st n ls)) <= mc_refused (fst st) + Z.of_nat (length ls) /\
  mc_overflow (fst st) <= mc_overflow (fst (m_lines st n ls)) <= mc_overflow (fst st) + Z.of_nat (length ls).
Proof.
  induction ls as [|l r IH]; intros st n; cbn [m_lines length]; [lia|].
  pose proof (l02m_line_cnt st (n + 1) l) as H1. pose proof (IH (m_line st (n + 1) l) (n + 1)) as H2. lia.
Qed.

Lemma l02m_file_gen mc s lab : mc_gen (m_file mc s lab) = mc_gen mc + 1.
Proof. unfold m_file. cbv zeta. exact (proj1 (l02m_lines_cnt _ _ _)). Qed.

Lemma l02m_file_refused mc s lab : nulfree s ->
  mc_refused mc <= mc_refused (m_file mc s lab) <= mc_refused mc + Z.of_nat (length s).
Proof.
  intros Hn. pose proof (lines_props s Hn) as [_ Hl]. unfold m_file. cbv zeta.
  match goal with |- context [m_lines ?st ?n ?ls] => pose proof (l02m_lines_cnt ls st n) as H end.
  cbn [fst mc_refused] in H. lia.
Qed.

Lemma l02m_file_overflow mc s lab : nulfree s ->
  mc_overflow mc <= mc_overflow (m_file mc s lab) <= mc_overflow mc + Z.of_nat (length s).
Proof.
  intros Hn. pose proof (lines_props s Hn) as [_ Hl]. unfold m_file. cbv zeta.
  match goal with |- context [m_lines ?st ?n ?ls] => pose proof (l02m_lines_cnt ls st n) as H end.
  cbn [fst mc_overflow] in H. lia.
Qed.

(** After k drop-in turns: the reader and the model agree (SegModel.conf_rel), gen = k, and refused and overflow
    at most 65535 a turn. *)
Lemma l02m_run inp k :
  conf_rel (seg_rc (seg_run inp k)) (seg_mc (seg_run inp k)) /\
  mc_gen (seg_mc (seg_run inp k)) = Z.of_nat k /\
  0 <= mc_refused (seg_mc (seg_run inp k)) <= 65535 * Z.of_nat k /\
  0 <= mc_overflow (seg_mc (seg_run inp k)) <= 65535 * Z.of_nat k.
Proof.
  induction k as [|k IH].
  - cbn [seg_run seg_rc seg_mc fst snd]. split; [exact conf_rel0|]. cbn. lia.
  - cbn [seg_run]. revert IH. destruct (seg_run inp k) as [[c mc] ret]. cbn [seg_rc seg_mc fst snd].
    intros (Hc & Hg & Hr & Ho).
    destruct (l02m_turn_ok inp k) as (Hn & Hl & Hb).
    pose proof (l02m_file_gen mc (seg_txt inp k) (seg_label inp k)) as G.
    pose proof (l02m_file_refused mc (seg_txt inp k) (seg_label inp k) Hn) as R.
    pose proof (l02m_file_overflow mc (seg_txt inp k) (seg_label inp k) Hn) as O.
    pose proof (file_rel c mc (seg_txt inp k) (seg_label inp k) (seg_label inp k) Hc Hn Hl eq_refl
                         (rd_label_ok _ Hb)) as HF.
    revert HF. unfold seg_turn_step. cbv beta iota zeta.
    destruct (r_parse_file c (seg_txt inp k) (seg_label inp k)) as [c1 n]. cbn [seg_rc seg_mc fst snd].
    intros (H1 & _). split; [exact H1|]. lia.
Qed.

(** ** The seven lemmas the slot side reads *)
Lemma l02m_np : forall inp f,
  0 <= seg_txt_n inp f <= seg_turn_np inp f /\ seg_turn_np inp f <= Z.of_nat (length (seg_turn_tail inp f)).
Proof.
  intros inp f. unfold seg_txt_n, seg_turn_np. pose proof (l02m_txt_le inp f) as H.
  pose proof (l02m_take_len (seg_turn_tail inp f) (seg_turn_len inp f)) as [H1 _]. lia.
Qed.

Lemma l02m_tail_len : forall inp f, (length (seg_turn_tail inp f) <= length inp)%nat.
Proof.
  intros inp f. destruct (l02m_tail_sfx inp f) as [j Hj]. rewrite Hj, length_skipn, l02m_in_len. lia.
Qed.

Lemma l02m_cur_S inp f : seg_cur inp (S f) = snd (fuzz_take (seg_turn_tail inp f) (seg_turn_len inp f)).
Proof. unfold seg_cur. rewrite l02m_skip_S. reflexivity. Qed.

Lemma l02m_cur_next : forall inp p f,
  seg_cur_at inp p (S f) = seg_turn_at inp p f + seg_turn_np inp f /\
  seg_cur_n inp (S f) = Z.of_nat (length (seg_turn_tail inp f)) - seg_turn_np inp f.
Proof.
  intros inp p f. unfold seg_cur_at, seg_cur_n, seg_turn_at, seg_turn_np. rewrite l02m_cur_S.
  pose proof (l02m_take_len (seg_turn_tail inp f) (seg_turn_len inp f)) as [H1 H2]. lia.
Qed.

Lemma l02m_text_bytes : forall inp f, Z.of_nat f < seg_nfiles inp ->
  zb (seg_txt inp f) = firstn (length (seg_txt inp f)) (skipn (length inp - length (seg_turn_tail inp f)) inp).
Proof.
  intros inp f Hf. rewrite (proj1 (l02m_txt_in inp f Hf)), l02m_take_fst.
  generalize (Nat.min (Z.to_nat (seg_turn_len inp f)) (length (seg_turn_tail inp f))) as m. intros m.
  pose proof (l02m_tail_zs inp f) as HT.
  set (K := (length inp - length (seg_turn_tail inp f))%nat) in *. clearbody K.
  rewrite HT. apply l02m_text_gen.
Qed.

Lemma l02m_model : forall inp f, Z.of_nat f < seg_nfiles inp ->
  L02_model (seg_txt inp f) (seg_lb inp f) (seg_rc (seg_run inp f)) (seg_mc (seg_run inp f)).
Proof.
  intros inp f Hf. pose proof (l02m_nfiles inp) as HN.
  destruct (l02m_turn_ok inp f) as (_ & Hl & Hb).
  destruct (l02m_run inp f) as (Hc & Hg & Hr & Ho).
  destruct Hc as (_ & _ & _ & Hov & Href & _ & _ & Hgen).
  unfold L02_model. rewrite Hov, Href, Hgen.
  split; [apply l02m_txt_ok, Hf|].
  split; [enough (H65 : (length (seg_txt inp f) <= Z.to_nat 65535)%nat) by exact H65; lia|].
  split; [exact Hb|].
  change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648.
  change (2 ^ 17) with 131072. change (2 ^ 18) with 262144. lia.
Qed.

Lemma l02m_after : forall inp f,
  seg_after inp f = l02_step (seg_txt inp f) (seg_lb inp f) (Z.of_nat f + 1 =? seg_nfiles inp) (seg_run inp f).
Proof. intros inp f. unfold seg_after. rewrite Nat2Z.inj_succ. reflexivity. Qed.
