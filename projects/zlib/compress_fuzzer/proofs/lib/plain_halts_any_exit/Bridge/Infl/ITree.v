(** * Bridge.Infl.ITree — pair I15 of PAIRS.md: [inflate_table], S5 vs RT.

    S5's [Inftrees.inflate_table] writes packed codes into its 1444-entry [codes] array at
    absolute indices from [table]; RT's [Inftrees.it_model] writes [Code] records into a
    view of [state->codes] shifted to start at [table], which [Inflate.inf_table] writes
    back with [codes_wb].  Same return code; on success the same root bits, the same
    [next], tables related on all of [[0, ENOUGH)], and the new table has the [tview]
    shape (from S5's own [ItProof.run1]/[props]: coverage and [entry_shape]).

    S5 keeps [work] in the state and RT does not; S5's result does not depend on [work]'s
    incoming contents ([ItProof.run1] holds for any [work]), so only its length matters.

    Proof route (files [ITreePre], [ITreeStep], [ITreeLoop]): S5 proves its
    [inflate_table] equal to the abstract [ItDefs.it_abs] for any [work]
    ([ItSim2.inflate_table_abs]); [ITreeLoop.rt_model_abs] proves RT's [it_model]
    follows the same [it_abs], trip by trip, reusing S5's abstract theory.  The [tview]
    shape then comes from S5's [ItTable.it_abs_props] (coverage and [entry_shape]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState Inftrees InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ItDefs ItGen ItSimPre ItSim2 ItTable.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Inftrees Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv ITreePre ITreeLoop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module IT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Inftrees.
Module ICov := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.InftreesCoverage.
Module RIT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Inftrees.

Definition ty_rt (ty : IS.codetype) : Z :=
  match ty with IS.CODES => RIT.CT_CODES | IS.LENS => RIT.CT_LENS | IS.DISTS => RIT.CT_DISTS end.

Definition ty_kind (ty : IS.codetype) : tkind :=
  match ty with IS.CODES => KCodes | IS.LENS => KLens | IS.DISTS => KDists end.

(** The largest [codes] each call site passes: 19, [nlen <= 286], [ndist <= 30]. *)
Definition ty_max (ty : IS.codetype) : Z :=
  match ty with IS.CODES => 19 | IS.LENS => 286 | IS.DISTS => 30 end.

(* ------------------------------------------------------------------------- *)
(* The [tview] shape, from S5's coverage and [entry_shape]                   *)
(* ------------------------------------------------------------------------- *)

Lemma land16_small : forall op, 0 <= op < 16 -> Z.land op 16 = 0.
Proof.
  intros op H. apply Z.eqb_eq. change 16 with (2 ^ 4). rewrite ItGen.land_pow2_eq0 by lia.
  rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma land240_small : forall op, 0 <= op < 16 -> Z.land op 240 = 0.
Proof.
  intros op H.
  assert (E : op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8
              \/ op = 9 \/ op = 10 \/ op = 11 \/ op = 12 \/ op = 13 \/ op = 14 \/ op = 15) by lia.
  repeat (destruct E as [->|E]; [reflexivity|]). subst. reflexivity.
Qed.

(** [IInv.tent] as a boolean, for the finite checks over [lext]/[lbase] and [dext]/[dbase]. *)
Definition tent_b (k : tkind) (op val : Z) : bool :=
  match k with
  | KCodes => true
  | KLens => ((Z.land op 16 =? 0) || ((Z.land op 15 <=? 5) && (val + 2 ^ Z.land op 15 <=? 259)))
             && ((op =? 0) || negb (Z.land op 16 =? 0) || negb (Z.land op 64 =? 0) || (Z.land op 240 =? 0))
  | KDists => negb (op =? 0)
              && ((Z.land op 16 =? 0)
                  || ((Z.land op 15 <=? 13) && (1 <=? val) && (val + 2 ^ Z.land op 15 <=? 32769)))
              && (negb (Z.land op 16 =? 0) || negb (Z.land op 64 =? 0) || (Z.land op 240 =? 0))
  end.

Lemma tent_b_sound : forall k e, tent_b k (IS.code_op e) (IS.code_val e) = true -> tent k e.
Proof.
  intros k e H. unfold tent. cbv zeta. destruct k; cbn [tent_b] in H; [exact I| |];
    repeat first [rewrite Bool.andb_true_iff in H | rewrite Bool.orb_true_iff in H
                 | rewrite Bool.negb_true_iff in H];
    rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_le in H; tauto.
Qed.

(** What a symbol entry ([op]/[val] from [lext]/[lbase], [dext]/[dbase]) must satisfy. *)
Definition sym_ok (k : tkind) (op val : Z) : bool := negb (tsub k op) && tent_b k op val.

Lemma sym_ok_sound : forall k e, sym_ok k (IS.code_op e) (IS.code_val e) = true ->
  tsub k (IS.code_op e) = false /\ tent k e.
Proof.
  intros k e H. unfold sym_ok in H. apply andb_prop in H as [H1 H2]. apply negb_true_iff in H1.
  split; [exact H1|]. apply tent_b_sound. exact H2.
Qed.

Lemma sym_entry_ok : forall ty s, 0 <= s < ICov.nsyms ty ->
  sym_ok (ty_kind ty) (fst (ICov.sym_entry ty s)) (snd (ICov.sym_entry ty s)) = true.
Proof.
  intros ty s Hs. destruct ty; cbn [ICov.sym_entry ICov.nsyms ty_kind] in *.
  - reflexivity.
  - destruct (Z.ltb_spec s 256); [reflexivity|]. destruct (Z.eqb_spec s 256); [reflexivity|]. cbn [fst snd].
    assert (Hall : forallb (fun j => sym_ok KLens (nth j IT.lext_l 0) (nth j IT.lbase_l 0)) (seq 0 31) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in Hall. apply Hall. apply in_seq. lia.
  - cbn [fst snd].
    assert (Hall : forallb (fun j => sym_ok KDists (nth j IT.dext_l 0) (nth j IT.dbase_l 0)) (seq 0 32) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in Hall. apply Hall. apply in_seq. lia.
Qed.

Lemma op64_ok : forall ty e, IS.code_op e = 64 -> tsub (ty_kind ty) (IS.code_op e) = false /\ tent (ty_kind ty) e.
Proof.
  intros ty e Hop. split.
  - rewrite Hop. destruct ty; reflexivity.
  - apply tent_b_sound. rewrite Hop. destruct ty; reflexivity.
Qed.

(** A root entry ([x < 2^root]). *)
Lemma shape_root : forall ty root U x e, 1 <= root <= 15 -> 0 <= x < 2 ^ root ->
  ICov.entry_shape ty root U x e ->
  IS.code_bits e <= root /\ tent (ty_kind ty) e /\
  (tsub (ty_kind ty) (IS.code_op e) = true ->
     IS.code_bits e = root /\ 1 <= IS.code_op e /\ root + IS.code_op e <= 15 /\
     2 ^ root <= IS.code_val e /\ IS.code_val e + 2 ^ IS.code_op e <= U).
Proof.
  intros ty root U x e Hr Hx
    [[s [len [Hs [Hl [Hop [Hval [[Hx1 [Hle Hb]]|[Hx1 _]]]]]]]] | [[Hx1 [Hb [Hop [Hv1 Hv2]]]] | [Hop [Hb [Hv Hr1]]]]].
  - assert (SO : sym_ok (ty_kind ty) (IS.code_op e) (IS.code_val e) = true)
      by (rewrite Hop, Hval; apply sym_entry_ok; exact Hs).
    destruct (sym_ok_sound _ _ SO) as [T1 T2].
    split; [lia|]. split; [exact T2|]. intros T. congruence.
  - lia.
  - split; [lia|]. split.
    + assert (L16 : Z.land (IS.code_op e) 16 = 0) by (apply land16_small; lia).
      assert (L240 : Z.land (IS.code_op e) 240 = 0) by (apply land240_small; lia).
      unfold tent. cbv zeta. destruct ty; cbn [ty_kind].
      * exact I.
      * split; [intros H; contradiction | intros; exact L240].
      * split; [lia|]. split; [intros H; contradiction | intros; exact L240].
    + intros _. repeat split; lia.
  - destruct (op64_ok ty e Hop) as [T1 T2].
    split; [lia|]. split; [exact T2|]. intros T. congruence.
Qed.

(** A sub-table entry ([2^root <= z]). *)
Lemma shape_sub : forall ty root U z e, 1 <= root <= 15 -> 2 ^ root <= z ->
  ICov.entry_shape ty root U z e ->
  IS.code_bits e <= 15 - root /\ tsub (ty_kind ty) (IS.code_op e) = false /\ tent (ty_kind ty) e.
Proof.
  intros ty root U z e Hr Hz
    [[s [len [Hs [Hl [Hop [Hval [[Hx1 _]|[_ [Hlt Hb]]]]]]]]] | [[Hx1 _] | [Hop [Hb [Hv Hr1]]]]].
  - lia.
  - assert (SO : sym_ok (ty_kind ty) (IS.code_op e) (IS.code_val e) = true)
      by (rewrite Hop, Hval; apply sym_entry_ok; exact Hs).
    split; [lia|]. exact (sym_ok_sound _ _ SO).
  - lia.
  - split; [lia|]. exact (op64_ok ty e Hop).
Qed.

Lemma tview_of : forall ty ws toff bits' table (a : arr) (g : Z -> RBa.Code),
  1 <= bits' <= 15 -> 0 <= table -> table + 2 ^ bits' <= toff -> toff <= arr_len a ->
  (forall i, table <= i < toff -> In i (map fst ws)) ->
  (forall i v, In (i, v) ws -> ICov.entry_shape ty bits' (toff - table) (i - table) v) ->
  (forall x, 0 <= x < toff - table -> arr_get (ItDefs.applyw ws a) (table + x) = RBa.code_enc (g x)) ->
  (forall x, code_rng (g x)) ->
  tview (fun x => arr_get (ItDefs.applyw ws a) (table + x)) g bits' (ty_kind ty).
Proof.
  intros ty ws toff bits' table a g Hb Ht Hlo Hhi Hcov Hsh Hrel Hrng.
  assert (SH : forall x, 0 <= x < toff - table ->
            ICov.entry_shape ty bits' (toff - table) x (arr_get (ItDefs.applyw ws a) (table + x))).
  { intros x Hx.
    assert (Hin : In (table + x) (map fst ws)) by (apply Hcov; lia).
    assert (Hr : 0 <= table + x < arr_len a) by lia.
    pose proof (ItGen.applyw_all (fun i v => ICov.entry_shape ty bits' (toff - table) (i - table) v)
                  ws a (table + x) Hsh Hin Hr) as P.
    cbv beta in P. replace (table + x - table) with x in P by lia. exact P. }
  unfold tview. cbv beta. split; [exact Hb|]. intros x Hx.
  assert (Hx' : 0 <= x < toff - table) by lia.
  destruct (shape_root ty bits' (toff - table) x _ Hb Hx (SH x Hx')) as [R1 [R2 R3]].
  split; [apply Hrel; exact Hx'|]. split; [apply Hrng|]. split; [exact R1|]. split; [exact R2|].
  intros T. destruct (R3 T) as [L1 [L2 [L3 [L4 L5]]]].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  intros y Hy. cbv zeta.
  assert (Hz : 0 <= IS.code_val (arr_get (ItDefs.applyw ws a) (table + x)) + y < toff - table) by lia.
  assert (Hz2 : 2 ^ bits' <= IS.code_val (arr_get (ItDefs.applyw ws a) (table + x)) + y) by lia.
  destruct (shape_sub ty bits' (toff - table) _ _ Hb Hz2 (SH _ Hz)) as [S1 [S2 S3]].
  split; [apply Hrel; exact Hz|]. split; [apply Hrng|]. split; [exact S1|]. split; [exact S2 | exact S3].
Qed.

Lemma inflate_table_sim : forall ty lens lensR ofs codes tbl tc table bits work o,
  0 < codes <= ty_max ty -> 0 <= ofs -> ofs + codes <= NLENS ->
  (forall i, 0 <= i < codes -> arr_get lens (ofs + i) = lensR i /\ 0 <= lensR i <= 15) ->
  (ty = IS.CODES -> forall i, 0 <= i < codes -> lensR i <= 7) ->
  arr_len tbl = ENOUGH -> tbl_rel tbl tc 0 ENOUGH -> (forall i, code_rng (tc i)) ->
  0 <= table -> table + ICov.it_room ty <= ENOUGH ->
  arr_len work = NWORK -> 1 <= bits <= 15 -> (ty = IS.CODES -> 7 <= bits) ->
  RIT.it_model (ty_rt ty) lensR codes bits (fun i => tc (table + i)) = Some o ->
  let '(ret, tbl', next, bits', work') := IT.inflate_table ty lens ofs codes tbl table bits work in
  ret = RIT.o_ret o /\
  (RIT.o_ret o = 0 ->
     bits' = RIT.o_bits o /\ next = table + RIT.o_used o /\ next <= table + ICov.it_room ty
     /\ arr_len tbl' = ENOUGH /\ arr_len work' = NWORK
     /\ tbl_rel tbl' (RI.codes_wb tc table (RIT.o_tbl o)) 0 ENOUGH
     /\ (forall i, code_rng (RI.codes_wb tc table (RIT.o_tbl o) i))
     /\ tview (fun x => arr_get tbl' (table + x))
              (fun x => RI.codes_wb tc table (RIT.o_tbl o) (table + x)) bits' (ty_kind ty)).
Proof.
  intros ty lens lensR ofs codes tbl tc table bits work o Hc Hofs Hofs2 Hlens H7 Hlen Hrel Hrng Ht0 Htr Hw
    Hbits Hb7 Hmod.
  assert (Hty : ty_rt ty = rtype ty) by (destruct ty; reflexivity). rewrite Hty in Hmod.
  assert (HC19 : ty = IS.CODES -> codes <= 19) by (intros ->; cbn [ty_max] in Hc; lia).
  assert (Hcodes : 0 <= codes <= 288) by (destruct ty; cbn [ty_max] in Hc; lia).
  assert (HL : forall i, ofs <= i < ofs + codes -> 0 <= arr_get lens i <= 15).
  { intros i Hi. destruct (Hlens (i - ofs) ltac:(lia)) as [E R]. replace (ofs + (i - ofs)) with i in E by lia.
    rewrite E. exact R. }
  assert (Hlr : forall i, 0 <= i < codes -> lensR i = arr_get lens (ofs + i))
    by (intros i Hi; symmetry; apply (Hlens i Hi)).
  assert (Hwk : codes <= arr_len work) by (rewrite Hw; unfold NWORK; lia).
  pose proof (ItSim2.inflate_table_abs ty lens ofs codes (ItDefs.lens_list lens ofs codes)
                (ItDefs.wl_of (ItDefs.lens_list lens ofs codes)) table bits Hcodes HL eq_refl eq_refl HC19 Hbits
                tbl work Hwk) as R1.
  pose proof (rt_model_abs ty lens ofs codes lensR bits tc table tbl o Hcodes HL Hlr HC19 Hbits Ht0 Hlen Hrel Hrng Hmod)
    as RM.
  assert (Hok : ItTable.ty_ok ty (ItDefs.lens_list lens ofs codes) bits).
  { assert (ENC : ItDefs.NC (ItDefs.lens_list lens ofs codes) = codes) by (apply ItSimPre.NC_lens; lia).
    destruct ty; cbn [ItTable.ty_ok]; rewrite ENC; cbn [ty_max] in Hc; try lia.
    split; [lia|]. split; [apply Hb7; reflexivity|].
    unfold ItDefs.lens_list. apply Forall_forall. intros l Hl. apply in_map_iff in Hl as [n [<- Hn]].
    apply in_seq in Hn. destruct (Hlens (Z.of_nat n) ltac:(lia)) as [E _]. rewrite E. apply (H7 eq_refl). lia. }
  pose proof (ItTable.it_abs_props (ItDefs.wl_of (ItDefs.lens_list lens ofs codes)) (ItDefs.lens_list lens ofs codes)
                table bits (ItSimPre.Hll lens ofs codes _ _ Hcodes HL eq_refl eq_refl) eq_refl Hbits ty Hok) as PR.
  rewrite R1. clear R1.
  destruct (ItDefs.it_abs (ItDefs.wl_of (ItDefs.lens_list lens ofs codes)) (ItDefs.lens_list lens ofs codes) ty table bits)
    as [[[[ret ws] toff] bits'] ww].
  cbn beta iota in PR, RM |- *.
  destruct RM as [RM1 RM2]. split; [symmetry; exact RM1|]. intros Hok0. rewrite RM1 in Hok0.
  destruct (RM2 Hok0) as [Eb [Et [HT HR]]]. destruct (PR Hok0) as [P1 [P2 [P3 [P4 P5]]]].
  split; [symmetry; exact Eb|]. split; [exact Et|]. split; [lia|].
  split; [rewrite ItGen.arr_len_applyw; exact Hlen|]. split; [rewrite ItGen.arr_len_applyw; exact Hw|].
  split; [exact (proj2 HT)|].
  assert (HRw : forall i, code_rng (RI.codes_wb tc table (RIT.o_tbl o) i)).
  { intros i. unfold RI.codes_wb. destruct (table <=? i); [apply HR | apply Hrng]. }
  split; [exact HRw|].
  apply tview_of with (toff := toff).
  - exact P1.
  - exact Ht0.
  - lia.
  - rewrite Hlen. lia.
  - exact P4.
  - exact P5.
  - intros x Hx. apply (proj2 HT). lia.
  - intros x. apply HRw.
Qed.
