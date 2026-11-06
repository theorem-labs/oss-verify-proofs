From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP.
Import ListNotations.
Open Scope Z_scope.

(* Transport of the asan premises across a run that writes only W' (munch W' m m'). *)

Lemma fl_out_lo : forall W' lo hi x, sub_fp W' [(lo, hi)] -> (x < lo \/ hi <= x) -> outside W' x.
Proof. intros W' lo hi x Hs Hx. apply Hs. cbn. split; [lia | exact I]. Qed.

Lemma fl_bytes : forall W m m' A bs,
  bytes_at rsegs m A bs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs (Ha & Hl & H) Hm Hd. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm.
  - apply H. exact Hi.
  - rewrite wa_unsigned by lia. apply Hd. lia.
Qed.

Lemma fl_shadow_out : forall W' lo hi x, sub_fp W' [(lo, hi)] -> HIGHMEM_BEG <= lo -> in_shadow x -> outside W' x.
Proof.
  intros W' lo hi x Hs Hlo Hx. apply (fl_out_lo W' lo hi x Hs). left.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
Qed.

Lemma fl_addressable : forall W m m' p n,
  addressable m p n -> munch W m m' -> (forall x, in_shadow x -> outside W x) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hs.
Qed.

Lemma fl_shadow_rw : forall W m m',
  shadow_rw m -> munch W m m' -> wmono rsegs m m' -> (forall x, in_shadow x -> outside W x) -> shadow_rw m'.
Proof.
  intros W m m' H Hm Hw HW a Ha. destruct (H a Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  exists b. pose proof (rt_shadow_bound _ Ha) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Ha.
Qed.

Lemma fl_asan_cells : forall W m m',
  asan_cells m -> munch W m m' -> (forall x, RT_LO <= x < RT_HI -> outside W x) -> asan_cells m'.
Proof.
  intros W m m' H Hm HW.
  unfold asan_cells in *.
  repeat match goal with
  | Hc : _ /\ _ |- _ => destruct Hc
  end.
  unfold CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND, GOT_HIEND, MIDBEG,
    GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET, GOT_REAL_MEMSET in *.
  repeat match goal with |- _ /\ _ => split end;
    (eapply fl_bytes; [eassumption | exact Hm | intros x Hx; apply HW;
       rewrite ?length_le8, ?length_le4 in Hx; cbn [length] in Hx; unfold RT_LO, RT_HI; lia]).
Qed.

(* A cell of the runtime: transported when [lo, hi) is apart from it (one of the ly_dj facts in the context). *)
Ltac fl_cell Hm Hs :=
  eapply fl_bytes; [eassumption | exact Hm |
    let x := fresh "x" in let Hx := fresh "Hx" in
    intros x Hx; apply (fl_out_lo _ _ _ x Hs);
    rewrite ?length_app, ?length_le8, ?length_le4 in Hx; cbn [length] in Hx;
    match goal with Hd : ly_dj _ _ _ _ |- _ => unfold ly_dj in Hd; lia end].

(* The class-c state survives writes outside the side stack. *)
Lemma fl_cls : forall W' m m' FS c, (forall x, FS <= x < FS + FS_SIZE -> outside W' x) -> munch W' m m' ->
  fp_cls m FS c -> fp_cls m' FS c.
Proof.
  intros W' m m' FS c BEL Hm (Hc & h & flags & HH & HF & HFl & HFb).
  split; [exact Hc|]. exists h, flags.
  assert (B : FS <= fs_hint FS c /\ fs_hint FS c + 8 <= FS + FS_SIZE /\
              FS <= fs_flag FS c 0 /\ fs_flag FS c 0 + fs_M c <= FS + FS_SIZE).
  { unfold fs_hint, fs_flag, fs_M, FS_SIZE. destruct c as [|[|[|[|[|[|[|c]]]]]]]; simpl; lia. }
  split; [eapply fl_bytes; [exact HH | exact Hm | intros x Hx; apply BEL; rewrite length_le8 in Hx; lia]|].
  split; [eapply fl_bytes; [exact HF | exact Hm | intros x Hx; apply BEL; lia]|].
  split; assumption.
Qed.

(* fp survives writes inside its window [lo, hi). *)
Lemma fl_fp : forall cs m m' TP FS lo hi W0 D W',
  fp cs m TP FS lo hi ((lo, hi) :: W0) D -> munch W' m m' -> wmono rsegs m m' -> sub_fp W' [(lo, hi)] ->
  fp cs m' TP FS lo hi ((lo, hi) :: W0) D.
Proof.
  intros cs m m' TP FS lo hi W0 D W' (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd &
    HDd) Hm Hw Hs.
  exists DT, TS, C, T, DB, k.
  (* the ly_dj facts of [lo, hi) against each range of fp_tls and the header *)
  pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
  cbn [fp_tls app] in Hw0.
  repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
  assert (BEL : forall x, FS <= x < FS + FS_SIZE -> outside W' x)
    by (intros x Hx; apply (fl_out_lo W' lo hi x Hs); lia).
  unfold asan_tls_cells in HT.
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  split.
  { unfold asan_tls_cells.
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [exact T6|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [destruct T11 as (tb & te & T11); exists tb, te; fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|].
    split; [fl_cell Hm Hs|]. split; [fl_cell Hm Hs|]. split; [exact T18|]. fl_cell Hm Hs. }
  split; [fl_cell Hm Hs|].
  split.
  { unfold fs_place in *. destruct HP as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|].
    split; [exact P3|]. split; [exact P4|]. eapply stk_transport; [exact P5 | exact Hm | exact Hw |].
    intros x Hx. left. apply BEL. exact Hx. }
  split; [eapply fl_bytes; [exact H88 | exact Hm | intros x Hx; apply BEL; rewrite ?length_le8 in Hx;
                             unfold FS_SIZE; lia]|].
  split; [eapply fl_bytes; [exact H96 | exact Hm | intros x Hx; apply BEL; cbn [length] in Hx;
                             unfold FS_SIZE; lia]|].
  split; [exact (Forall_impl _ (fun c => fl_cls W' m m' FS c BEL Hm) HCL)|].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* fp with other data ranges D'. *)
Lemma fl_fp_D : forall cs m TP FS lo hi W D D',
  fp cs m TP FS lo hi W D -> fp_dj D' (fp_w cs FS) -> fp cs m TP FS lo hi W D'.
Proof.
  intros cs m TP FS lo hi W D D' (DT & TS & C & T & DB & k & H) HD.
  exists DT, TS, C, T, DB, k.
  repeat match goal with
  | Hc : _ /\ _ |- _ => destruct Hc
  end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma fl_fp_dj : forall cs m TP FS lo hi W D, fp cs m TP FS lo hi W D -> fp_dj D (fp_w cs FS).
Proof.
  intros cs m TP FS lo hi W D (DT & TS & C & T & DB & k & H).
  repeat match goal with
  | Hc : _ /\ _ |- _ => destruct Hc
  end.
  assumption.
Qed.

(* A sub-range of a range apart from fp_w is apart from it. *)
Lemma fl_dj_sub : forall a b a' b' X, fp_dj [(a, b)] X -> a <= a' -> b' <= b -> a' <= b' -> fp_dj [(a', b')] X.
Proof.
  intros a b a' b' X H H1 H2 H3. unfold fp_dj in *. inversion H as [|w Wr Hw _]; subst.
  constructor; [|constructor]. rewrite Forall_forall in *. intros d Hd. pose proof (Hw d Hd) as Hx.
  unfold ly_dj in *. cbn [fst snd] in *. lia.
Qed.

Lemma fl_dj_cons : forall r D X, fp_dj (r :: D) X <-> fp_dj [r] X /\ fp_dj D X.
Proof.
  intros r D X. unfold fp_dj. split.
  - intros H. inversion H; subst. split; [constructor; [assumption | constructor] | assumption].
  - intros (H1 & H2). inversion H1; subst. constructor; assumption.
Qed.

(* Two byte lists at A, one read in m and one in m', where the run kept the bytes of [A, A + n): the same list. *)
Lemma fl_bytes_eq : forall W m m' A bs bs',
  bytes_at rsegs m A bs -> bytes_at rsegs m' A bs' -> munch W m m' -> length bs = length bs' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) -> bs = bs'.
Proof.
  intros W m m' A bs bs' H H' Hm Hl Hd.
  destruct (fl_bytes W m m' A bs H Hm Hd) as (_ & _ & H2). destruct H' as (_ & _ & H3).
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (H2 i Hi). apply H3. lia.
  - rewrite (proj2 (nth_error_None bs i) Hi). symmetry. apply nth_error_None. lia.
Qed.

Lemma fl_le8_eq : forall W m m' A (w w' : word),
  bytes_at rsegs m A (le8 w) -> bytes_at rsegs m' A (le8 w') -> munch W m m' ->
  (forall x, A <= x < A + 8 -> outside W x) -> w = w'.
Proof.
  intros W m m' A w w' H H' Hm Hd.
  assert (E : le8 w = le8 w').
  { apply (fl_bytes_eq W m m' A _ _ H H' Hm); [rewrite !length_le8; reflexivity|].
    rewrite length_le8. change (Z.of_nat 8) with 8. exact Hd. }
  rewrite <- (le_bytes_to_word_le8 w), E. apply le_bytes_to_word_le8.
Qed.

Lemma fl_le4_eq : forall W m m' A k k', 0 <= k < 2^32 -> 0 <= k' < 2^32 ->
  bytes_at rsegs m A (le4 (Z_to_bv 64 k)) -> bytes_at rsegs m' A (le4 (Z_to_bv 64 k')) -> munch W m m' ->
  (forall x, A <= x < A + 4 -> outside W x) -> k = k'.
Proof.
  intros W m m' A k k' Hk Hk' H H' Hm Hd.
  assert (E : le4 (Z_to_bv 64 k) = le4 (Z_to_bv 64 k')).
  { apply (fl_bytes_eq W m m' A _ _ H H' Hm); [rewrite !length_le4; reflexivity|].
    rewrite length_le4. change (Z.of_nat 4) with 4. exact Hd. }
  pose proof (le_bytes_to_word_le4 (Z_to_bv 64 k)) as E1. pose proof (le_bytes_to_word_le4 (Z_to_bv 64 k')) as E2.
  rewrite E in E1. rewrite E1 in E2. rewrite !unsigned_lit in E2 by lia. rewrite !Z.mod_small in E2 by lia.
  exact E2.
Qed.

(* A byte of a thread cell is outside the run's writes W': one of the ly_dj facts of fp's window (OUT) covers it. *)
Ltac fl_tls_out OUT :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; match goal with Hd : ly_dj _ _ _ _ |- _ => apply (OUT _ _ Hd); lia end.

(* The tls premise of a contract (the thread cells that fp names apart from a list X: fp_w cs FS and the shadow of
   the window) survives writes inside fp's window [lo, hi): the cells keep their bytes, so the pointers read from
   them are those of m. *)
Lemma fl_tls : forall cs m m' TP FS lo hi W0 D W' X,
  fp cs m TP FS lo hi ((lo, hi) :: W0) D -> munch W' m m' -> sub_fp W' [(lo, hi)] ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) X) ->
  forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) X.
Proof.
  intros cs m m' TP FS lo hi W0 D W' X (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
    Hm Hs Htls DT TS C T DB k HT.
  pose proof HT0 as HT0c.
  pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
  cbn [fp_tls app] in Hw0.
  repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
  assert (OUT : forall a b, ly_dj lo hi a b -> forall x, a <= x < b -> outside W' x)
    by (intros a b Hab x Hx; apply (fl_out_lo W' lo hi x Hs); unfold ly_dj in Hab; lia).
  destruct HT0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
    & A18 & A19).
  destruct HT as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17
    & B18 & B19).
  assert (EDT : DT0 = DT) by (apply (fl_le8_eq W' m m' (TP - 8) DT0 DT A3 B3 Hm); fl_tls_out OUT).
  assert (Ek : k0 = k) by (apply (fl_le4_eq W' m m' TSD_KEY k0 k A6 B6 A7 B7 Hm); fl_tls_out OUT).
  assert (ETS : TS0 = TS) by (apply (fl_le8_eq W' m m' (TP - 88) TS0 TS A8 B8 Hm); fl_tls_out OUT).
  subst DT0 k0 TS0.
  assert (EC : C0 = C) by (apply (fl_le8_eq W' m m' (bv_unsigned TS + 8 * k) C0 C A9 B9 Hm); fl_tls_out OUT).
  subst C0.
  assert (ET : T0 = T) by (apply (fl_le8_eq W' m m' (bv_unsigned C + 152) T0 T A10 B10 Hm); fl_tls_out OUT).
  assert (EDB : DB0 = DB) by (apply (fl_le8_eq W' m m' (TP + 8) DB0 DB A17 B17 Hm); fl_tls_out OUT).
  subst T0 DB0.
  exact (Htls DT TS C T DB k HT0c).
Qed.

(* The general forms: writes inside any range of fp's W (not only its window), and fp at a callee's return. *)

Lemma fl_out_app : forall A B x, outside A x -> outside B x -> outside (A ++ B) x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x HA HB; cbn [app outside] in *; [exact HB|].
  destruct HA as [H1 H2]. split; [exact H1 | exact (IH B x H2 HB)].
Qed.

(* A byte of a range of L is outside every W apart from L (fl_dj_out), and outside every X that L is apart from
   (fl_dj_out_r). *)
Lemma fl_dj_out : forall W L a b x, fp_dj W L -> In (a, b) L -> a <= x < b -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros L a b x H Hin Hx; cbn [outside]; [exact I|].
  unfold fp_dj in H. apply Forall_cons_iff in H as [H1 H2]. split.
  - rewrite Forall_forall in H1. pose proof (H1 _ Hin) as D. unfold ly_dj in D. cbn [fst snd] in D. lia.
  - exact (IH L a b x H2 Hin Hx).
Qed.

Lemma fl_dj_out_r : forall L X a b x, fp_dj L X -> In (a, b) L -> a <= x < b -> outside X x.
Proof.
  intros L X a b x H Hin Hx. unfold fp_dj in H. rewrite Forall_forall in H. pose proof (H _ Hin) as H1.
  cbn [fst snd] in H1. clear H Hin. induction X as [|[lo hi] X IH]; cbn [outside]; [exact I|].
  apply Forall_cons_iff in H1 as [D H1]. unfold ly_dj in D. cbn [fst snd] in D. split; [lia | exact (IH H1)].
Qed.

(* Every byte of every range of L is outside the run's writes W' when W' is inside W and W is apart from L. *)
Lemma fl_cols : forall W W' L, fp_dj W L -> sub_fp W' W ->
  Forall (fun d => forall x, fst d <= x < snd d -> outside W' x) L.
Proof.
  intros W W' L H Hs. apply Forall_forall. intros [a b] Hin x Hx. apply Hs. exact (fl_dj_out W L a b x H Hin Hx).
Qed.

(* A cell's bytes are outside the writes: one of the facts O (from fl_cols) covers them. *)
Ltac fl_col :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; rewrite ?length_app, ?length_le8, ?length_le4 in Hx; cbn [length] in Hx;
  match goal with O : forall y, _ <= y < _ -> outside _ y |- _ => apply O; lia end.

Ltac fl_cellO Hm := eapply fl_bytes; [eassumption | exact Hm | fl_col].

(* The thread cells keep their bytes under writes they are apart from: the pointers read from them are the same. *)
Lemma fl_tls_same : forall m m' W' TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k,
  asan_tls_cells m TP DT0 TS0 C0 T0 DB0 k0 -> asan_tls_cells m' TP DT TS C T DB k -> munch W' m m' ->
  Forall (fun d => forall x, fst d <= x < snd d -> outside W' x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0) ->
  DT0 = DT /\ TS0 = TS /\ C0 = C /\ T0 = T /\ DB0 = DB /\ k0 = k.
Proof.
  intros m m' W' TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc.
  cbn [fp_tls] in Hc.
  repeat (let O := fresh "O" in apply Forall_cons_iff in Hc; destruct Hc as [O Hc]; cbn [fst snd] in O).
  destruct HT0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
    & A18 & A19).
  destruct HT as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17
    & B18 & B19).
  assert (EDT : DT0 = DT) by (apply (fl_le8_eq W' m m' (TP - 8) DT0 DT A3 B3 Hm); fl_col).
  assert (Ek : k0 = k) by (apply (fl_le4_eq W' m m' TSD_KEY k0 k A6 B6 A7 B7 Hm); fl_col).
  assert (ETS : TS0 = TS) by (apply (fl_le8_eq W' m m' (TP - 88) TS0 TS A8 B8 Hm); fl_col).
  subst DT0 k0 TS0.
  assert (EC : C0 = C) by (apply (fl_le8_eq W' m m' (bv_unsigned TS + 8 * k) C0 C A9 B9 Hm); fl_col).
  subst C0.
  assert (ET : T0 = T) by (apply (fl_le8_eq W' m m' (bv_unsigned C + 152) T0 T A10 B10 Hm); fl_col).
  assert (EDB : DB0 = DB) by (apply (fl_le8_eq W' m m' (TP + 8) DB0 DB A17 B17 Hm); fl_col).
  subst T0 DB0. repeat split.
Qed.

(* The tls premise survives writes inside fp's W (fl_tls for any range of W). *)
Lemma fl_tls_W : forall cs m m' TP FS lo hi W D W' X,
  fp cs m TP FS lo hi W D -> munch W' m m' -> sub_fp W' W ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) X) ->
  forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) X.
Proof.
  intros cs m m' TP FS lo hi W D W' X (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
    Hm Hs Htls DT TS C T DB k HT.
  pose proof (fl_cols W W' _ HWd Hs) as Hc. apply Forall_app in Hc as [Hc _].
  destruct (fl_tls_same m m' W' TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0. exact (Htls DT TS C T DB k HT0).
Qed.

(* The class-c state survives writes outside the side stack's header [FS, FS + 36864). *)
Lemma fl_cls_h : forall W' m m' FS c, (forall x, FS <= x < FS + 36864 -> outside W' x) -> munch W' m m' ->
  fp_cls m FS c -> fp_cls m' FS c.
Proof.
  intros W' m m' FS c BEL Hm (Hc & h & flags & HH & HF & HFl & HFb).
  split; [exact Hc|]. exists h, flags.
  assert (B : FS <= fs_hint FS c /\ fs_hint FS c + 8 <= FS + 36864 /\
              FS <= fs_flag FS c 0 /\ fs_flag FS c 0 + fs_M c <= FS + 36864).
  { unfold fs_hint, fs_flag, fs_M. destruct c as [|[|[|[|[|[|[|c]]]]]]]; simpl; lia. }
  split; [eapply fl_bytes; [exact HH | exact Hm | intros x Hx; apply BEL; rewrite length_le8 in Hx; lia]|].
  split; [eapply fl_bytes; [exact HF | exact Hm | intros x Hx; apply BEL; lia]|].
  split; assumption.
Qed.

(* stk survives writes whose bytes read back after the run. *)
Lemma fl_stk : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) Hm Hw HX. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  destruct (HX a Ha) as [Ho | Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* fp survives writes inside its W whose bytes on the side stack read back after the run (fl_fp for any range of
   W). *)
Lemma fl_fp_W : forall cs m m' TP FS lo hi W D W',
  fp cs m TP FS lo hi W D -> munch W' m m' -> wmono rsegs m m' -> sub_fp W' W ->
  (forall x, FS <= x < FS + FS_SIZE -> outside W' x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
  fp cs m' TP FS lo hi W D.
Proof.
  intros cs m m' TP FS lo hi W D W' (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd &
    HDd) Hm Hw Hs HRD.
  exists DT, TS, C, T, DB, k.
  pose proof (fl_cols W W' _ HWd Hs) as Hc.
  replace (fs_frame FS 0 0) with (FS + 36864) in Hc by (unfold fs_frame; lia).
  cbn [fp_tls app] in Hc.
  repeat (let O := fresh "O" in apply Forall_cons_iff in Hc; destruct Hc as [O Hc]; cbn [fst snd] in O).
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  split.
  { unfold asan_tls_cells.
    split; [fl_cellO Hm|]. split; [fl_cellO Hm|]. split; [fl_cellO Hm|]. split; [fl_cellO Hm|].
    split; [fl_cellO Hm|]. split; [exact T6|]. split; [fl_cellO Hm|]. split; [fl_cellO Hm|].
    split; [fl_cellO Hm|]. split; [fl_cellO Hm|].
    split; [destruct T11 as (tb & te & T11); exists tb, te; fl_cellO Hm|].
    split; [fl_cellO Hm|]. split; [fl_cellO Hm|]. split; [fl_cellO Hm|]. split; [fl_cellO Hm|].
    split; [fl_cellO Hm|]. split; [fl_cellO Hm|]. split; [exact T18|]. fl_cellO Hm. }
  split; [fl_cellO Hm|].
  split.
  { destruct HP as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|].
    split; [exact P3|]. split; [exact P4|]. exact (fl_stk W' m m' FS (FS + FS_SIZE) P5 Hm Hw HRD). }
  split; [fl_cellO Hm|].
  split; [fl_cellO Hm|].
  split; [exact (Forall_impl _ (fun c => fl_cls_h W' m m' FS c ltac:(assumption) Hm) HCL)|].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* fp at a callee's return: the run wrote only W, fp_w cs FS and Y (the thread cells are apart from the last two),
   and the callee's fp at the return gives the side stack's state. *)
Lemma fl_fp_ret : forall cs m m' TP FS lo hi W D Y Wm lo' hi' W' D',
  fp cs m TP FS lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y)) ->
  munch Wm m m' -> sub_fp Wm (W ++ fp_w cs FS ++ Y) ->
  fp cs m' TP FS lo' hi' W' D' -> fp cs m' TP FS lo hi W D.
Proof.
  intros cs m m' TP FS lo hi W D Y Wm lo' hi' W' D'
    (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & HFS & HA & HWd & HDd) Htls Hm Hs
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & _ & _ & _ & _).
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a b] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a b x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a b x (Htls _ _ _ _ _ _ HT0) Hin Hx). }
  destruct (fl_tls_same m m' Wm TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0.
  exists DT, TS, C, T, DB, k.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* fp for a callee's window [lo', hi') inside [lo, hi), with writes W' and data ranges D' that W and D cover. *)
Lemma fl_fp_sub : forall cs m TP FS lo hi W D lo' hi' W' D',
  fp cs m TP FS lo hi W D -> lo <= lo' -> hi' <= hi ->
  (forall X, fp_dj W X -> fp_dj W' X) -> (forall X, fp_dj D X -> fp_dj D' X) ->
  fp cs m TP FS lo' hi' W' D'.
Proof.
  intros cs m TP FS lo hi W D lo' hi' W' D' (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA &
    HWd & HDd) H1 H2 HW HD.
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|]. split; [exact H96|].
  split; [exact HCL|]. split; [lia|]. split; [intros a Ha; apply HA; lia|].
  split; [apply HW; exact HWd | apply HD; exact HDd].
Qed.

(* The last range of an apart list shrunk. *)
Lemma fl_dj_last : forall L X a b a' b', fp_dj L (X ++ [(a, b)]) -> a <= a' -> b' <= b ->
  fp_dj L (X ++ [(a', b')]).
Proof.
  intros L X a b a' b' H H1 H2. unfold fp_dj in *. eapply Forall_impl; [|exact H]. intros w Hw. cbn beta in Hw.
  apply Forall_app in Hw as [Hx Hy]. apply Forall_app. split; [exact Hx|].
  apply Forall_cons_iff in Hy as [Hy _]. constructor; [|constructor]. unfold ly_dj in *. cbn [fst snd] in *. lia.
Qed.

(* fp survives the inline release of an own side-stack frame: the run writes only W, the class bytes fp_w cs FS (the
   magic word into the frame, the shadow rewrite, the flag cleared through [fr + B - 8]) and the window's shadow; the
   thread cells and the header points FS+88/FS+96 are apart from all of these, the side stack stays readable, and the
   hint and the flag bytes read back as 0/1 at m'. Reusable across classes (cs). *)
Lemma fl_fp_free : forall cs m m' TP FS lo hi W D Wm,
  fp cs m TP FS lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)])) ->
  munch Wm m m' -> wmono rsegs m m' ->
  sub_fp Wm (W ++ fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)]) ->
  (forall x, FS + 80 <= x < FS + 104 -> outside Wm x) ->
  (forall x, FS <= x < FS + FS_SIZE -> outside Wm x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
  (forall c, In c cs ->
     (exists h', bytes_at rsegs m' (fs_hint FS c) (le8 h')) /\
     (exists flags', bytes_at rsegs m' (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
        Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags')) ->
  fp cs m' TP FS lo hi W D.
Proof.
  intros cs m m' TP FS lo hi W D Wm (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HApp & HWd & HDd)
    Htls MU WM Hs O88 HRD Hcls.
  pose proof (Htls DT TS C T DB k HT) as TLSdj.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT TS C T DB k)).
  { apply Forall_forall. intros [a bnd] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a bnd x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a bnd x TLSdj Hin Hx). }
  cbn [fp_tls] in Hc.
  repeat (let O := fresh "O" in apply Forall_cons_iff in Hc; destruct Hc as [O Hc]; cbn [fst snd] in O).
  pose proof HCL as HCL'.
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  exists DT, TS, C, T, DB, k.
  split.
  { unfold asan_tls_cells.
    split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|].
    split; [fl_cellO MU|]. split; [exact T6|]. split; [fl_cellO MU|]. split; [fl_cellO MU|].
    split; [fl_cellO MU|]. split; [fl_cellO MU|].
    split; [destruct T11 as (tb & te & T11); exists tb, te; fl_cellO MU|].
    split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|].
    split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [exact T18|]. fl_cellO MU. }
  split; [fl_cellO MU|].
  split.
  { destruct HP as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exact P4|]. exact (fl_stk Wm m m' FS (FS + FS_SIZE) P5 MU WM HRD). }
  split; [fl_cellO MU|].
  split; [fl_cellO MU|].
  split.
  { apply Forall_forall. intros c Hin.
    pose proof (proj1 (Forall_forall _ _) HCL' c Hin) as HCc. destruct HCc as (Hc6 & _).
    destruct (Hcls c Hin) as ((h' & Hh') & (flags' & Hf' & Hl' & HF')).
    split; [exact Hc6|]. exists h', flags'. split; [exact Hh'|]. split; [exact Hf'|]. split; [exact Hl' | exact HF']. }
  split; [exact HFS|]. split; [exact HApp|]. split; [exact HWd | exact HDd].
Qed.

(* ----- Free-frame (fp_wx) transport (P9). ----- *)

Lemma outside_app_iff : forall A B x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x; cbn [app outside].
  - split; [intros H; split; [exact I | exact H] | intros [_ H]; exact H].
  - rewrite IH. tauto.
Qed.

Lemma sub_fp_app_l : forall A B R, sub_fp A B -> sub_fp (A ++ R) (B ++ R).
Proof.
  intros A B R H x HBR. apply outside_app_iff in HBR as [HB HR].
  apply outside_app_iff. split; [apply H; exact HB | exact HR].
Qed.

(* A write confined to fp_wx cs FS X ++ R is still confined to fp_w cs FS ++ R (fp_wx is fp_w minus the excluded
   frames and their shadow, so it covers no more; the lemma a caller needs the wider set for). *)
Lemma fl_munch_wx_w : forall cs FS X R m m',
  munch (fp_wx cs FS X ++ R) m m' -> munch (fp_w cs FS ++ R) m m'.
Proof.
  intros cs FS X R m m' H. eapply munch_weaken; [| exact H].
  apply sub_fp_app_l. apply fp_wx_sub_w.
Qed.

(* A byte of an excluded class-c frame is outside fp_wx [c] FS [(c, i)]: the frame interval is split out and the
   frame's bytes sit below every shadow interval (frame bytes < LOWMEM_END <= every shadow address). *)
Lemma fp_wx_hole_out : forall FS c i x,
  (c <= 6)%nat -> 0 <= i -> i + 1 <= fs_M c -> 0 <= FS -> fs_frame FS c (fs_M c) <= LOWMEM_END ->
  fs_frame FS c i <= x < fs_frame FS c (i + 1) ->
  outside (fp_wx [c] FS [(c, i)]) x.
Proof.
  intros FS c i x Hc Hi0 Hi1 HFS Hlow Hx.
  assert (HBpos : 0 < fs_B c)
    by (unfold fs_B; destruct c as [|[|[|[|[|[|[|c]]]]]]]; try (exfalso; lia); simpl; lia).
  assert (Hmono : forall a b, a <= b -> fs_frame FS c a <= fs_frame FS c b)
    by (intros a b Hab; unfold fs_frame; nia).
  assert (Hsep : fs_hint FS c + 8 <= fs_frame FS c 0 /\ fs_flag FS c 0 + fs_M c <= fs_frame FS c 0 /\
                 36864 <= fs_frame FS c 0).
  { unfold fs_hint, fs_flag, fs_frame, fs_B, fs_M; destruct c as [|[|[|[|[|[|[|c]]]]]]]; try (exfalso; lia);
      simpl; lia. }
  destruct Hsep as (Hhint & Hflag & HF0pos).
  pose proof (Hmono 0 i ltac:(lia)) as M0i.
  pose proof (Hmono i (i + 1) ltac:(lia)) as Mii1.
  pose proof (Hmono (i + 1) (fs_M c) ltac:(lia)) as Mi1M.
  assert (Hxlow : x < shadow_addr (fs_frame FS c 0)).
  { unfold shadow_addr, ASAN_K. unfold LOWMEM_END in Hlow. Z.div_mod_to_equations. lia. }
  apply (outside_of_cover (fp_wx [c] FS [(c, i)])
          [(fs_hint FS c, fs_hint FS c + 8); (fs_flag FS c 0, fs_flag FS c 0 + fs_M c);
           (fs_frame FS c 0, Z.min (fs_frame FS c i) (fs_frame FS c (fs_M c)));
           (Z.max (fs_frame FS c (i + 1)) (fs_frame FS c 0), fs_frame FS c (fs_M c));
           (shadow_addr (fs_frame FS c 0),
            Z.min (shadow_addr (fs_frame FS c i)) (shadow_addr (fs_frame FS c (fs_M c))));
           (Z.max (shadow_addr (fs_frame FS c (i + 1))) (shadow_addr (fs_frame FS c 0)),
            shadow_addr (fs_frame FS c (fs_M c)))] x).
  - intros r Hr. exists r. split; [| split; clear; lia].
    change (fp_wx [c] FS [(c, i)]) with (flat_map (fp_wx1 FS [(c, i)]) [c]) in Hr.
    cbn [flat_map] in Hr. rewrite app_nil_r in Hr.
    unfold fp_wx1 in Hr.
    replace (map snd (filter (fun ci => Nat.eqb (fst ci) c) [(c, i)])) with [i] in Hr
      by (cbn; rewrite Nat.eqb_refl; reflexivity).
    cbn [map] in Hr. unfold cut_ivls, nonempty in Hr. cbn [cut_ivls0] in Hr.
    apply in_app_or in Hr as [Hr | Hr].
    + cbn [In] in Hr |- *. destruct Hr as [<-|[<-|[]]]; tauto.
    + apply in_app_or in Hr as [Hr | Hr]; apply In_filter_drop in Hr;
        cbn [In] in Hr |- *; destruct Hr as [<-|[<-|[]]];
        repeat first [ left; reflexivity | right ].
  - cbn [outside fst snd]. repeat split; lia.
Qed.
