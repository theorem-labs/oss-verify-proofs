(* the zlib 1.4 twin of ZReproQ6W, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from ZReproQ6W), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * ZReproQ6W — Q6: the shared body walk (plumbing layer).

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-20).  The
    wrap-agnostic block-loop walk both face assemblies consume,
    HYPOTHESIZED on the residue Props (Q6HuffResidue) per the settled
    factoring: provable now from the landed legs; stage 4 discharges the
    residues later, making every consumer unconditional with no rework.

    This file builds bottom-up: iterate/loop composition, the step
    reduction at M_TYPE, the TOTAL case analysis of a TYPEDO trip
    (extending the landed zr_typedo_sound with the starvation-leave
    shape), the copy-loop sub-induction, then the walk with its two
    committed entries (M_TYPE primary; wrap-0 M_HEAD for the raw lane).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn InflateFast Inflate DeflateSpec
  StoredRt.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6B ZReproQ6C ZReproQ6D ZReproQ6E ZReproL0E ZReproQ6I.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6HuffResidue.
(* amendment #10, q7-decode as TL-confirmed carrier, 2026-08-20; owner
   (model-rt) review trails; spec = AMENDMENT-10-FREEZE.md :
   zr_body_entry gains the reader premises (haligned + compositional
   budget, appended last), zr_body_exit's agreement arm gains the flags
   clause (after h_wrap) and returns haligned + budget (appended last);
   the trips thread via GtBrAlign + the residue/fast-leg returns. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6W.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6HuffResidue14 Spec.PngModel.Inflate14 Spec.PngModel.Inflate14Iter ZReproQ6I14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   2.  The step reduction at M_TYPE and the TOTAL TYPEDO trip.
   ========================================================================== *)

(** The starvation-leave shape of a TYPEDO trip: ret rides untouched.
    Complements the landed [zr_typedo_sound] (which is conditional on
    [InfCont]) into a total case analysis; TYPEDO produces no other
    constructor. *)

(* ==========================================================================
   3.  The copy loop: from a COPY-mode state with [length] pinned, the
       model transfers exactly [length] bytes (or starves/fills — the
       absorbed arms), byte-for-byte the reader's next bytes, and lands
       at M_TYPE.
   ========================================================================== *)


(** The copy loop's exit shape, mirroring the residue style: either the
    whole pending length is transferred (the reader advances exactly
    those bytes, the output slice extends by exactly them, exit at
    M_TYPE), or an absorbed arm. *)
Definition zr_copy_exit14 (c : InfCtx) (q : InfSt) : Prop :=
  (exists k q',
     inf_iter14 k c q = Some q'
     /\ br_bytes (q_br q)
        = (map (fun m => br_in (q_br q) (br_next (q_br q) + Z.of_nat m))
               (seq 0 (Z.to_nat (u_length (s_cur (q_st q))))))
          ++ br_bytes (q_br q')
     /\ br_hold (q_br q') = br_hold (q_br q)
     /\ br_bits (q_br q') = br_bits (q_br q)
     /\ br_wf (q_br q')
     /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
        = ob_slice (q_ob q) 0 (o_put (q_ob q))
          ++ map (fun m => br_in (q_br q) (br_next (q_br q) + Z.of_nat m))
                 (seq 0 (Z.to_nat (u_length (s_cur (q_st q)))))
     /\ o_put (q_ob q') = o_put (q_ob q) + u_length (s_cur (q_st q))
     /\ o_put (q_ob q') + o_left (q_ob q')
        = o_put (q_ob q) + o_left (q_ob q)
     /\ 0 <= o_left (q_ob q')
     /\ h_mode (s_hdr (q_st q')) = M_TYPE
     /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
     /\ q_ret q' = q_ret q
     /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
     /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q))
     /\ w_whave (s_win (q_st q')) = w_whave (s_win (q_st q))
     /\ t_sane (s_tab (q_st q')) = t_sane (s_tab (q_st q))
     /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
     (* amendment #11: h_check/h_total frame conjuncts — carrier
        q7-decode; g1 census; q6 pre-ruling;
        #10 shape *)
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q)))
  \/ (exists n s, inf_loop14 n c q = Some s
        /\ match s with
           | InfLeave q2 => q_ret q2 = q_ret q
           | InfFuel => True
           | _ => False
           end).

(** Frame supplement to the landed [zr_copy_step]: a COPY trip touches
    cursor/reader/output only — the header scalars, return code, entry
    snapshots, window size all ride.  Stated over BOTH result arms so the
    loop's absorbed branch inherits ret-preservation too. *)

(** Prefix identification: equal-length prefixes of one list are equal. *)


(** THE COPY LOOP: the whole pending stored length transfers (with the
    reader/output accounting of [zr_copy_exit]), or the run exits into
    an absorbed arm. *)
Lemma zr_copy_loop14 : forall n c q,
  (Z.to_nat (u_length (s_cur (q_st q))) <= n)%nat ->
  zr_copy_entry q ->
  zr_copy_exit14 c q.
Proof.
  induction n as [|n IH]; intros c q Hn Hentry;
  pose proof Hentry as (Hwf & Hput & Hleft & Hlen & Hm);
  destruct (zr_copy_step q Hwf Hleft Hput Hlen)
    as [[E0 EC] | [EL | (c2 & q' & Hc2 & Hc2h & Hc2o & EC & HLen'
                         & HMode & HHold & HBits & HBytes & HWf'
                         & HPut' & HLeft' & HSlice)]].
  (* --- length 0: one step to M_TYPE (both n cases) --- *)
  1,4:
    left;
    exists 1%nat, (qmode q M_TYPE);
    rewrite E0; change (Z.to_nat 0) with 0%nat; cbn [seq map];
    (split;
     [ apply inf_iter14_one; rewrite (zr_step_at_copy14 c q Hm); exact EC |]);
    unfold qmode, qset_st; cbn [q_br q_ob q_st q_in q_out q_ret];
    repeat split; try reflexivity; try lia;
    try (rewrite app_nil_r; reflexivity);
    try (destruct Hwf as (Hw1 & Hw2 & Hw3 & Hw4); try lia;
         match goal with |- context [br_in ?b ?k] =>
           specialize (Hw4 k); lia end).
  (* --- starvation/fill leave (both n cases) --- *)
  1,3:
    right;
    exists 1%nat, (InfLeave q);
    (split;
     [ apply inf_loop14_one_exit;
       [ rewrite (zr_step_at_copy14 c q Hm); exact EL | exact I ]
     | reflexivity ]).
  (* --- transfer at n = 0: measure exhausted --- *)
  { exfalso.
    pose proof (Z2Nat.id (u_length (s_cur (q_st q))) ltac:(lia)) as HID.
    assert (HZ : Z.to_nat (u_length (s_cur (q_st q))) = 0%nat) by lia.
    rewrite HZ in HID. cbn in HID. lia. }
  (* --- transfer at n = S n: recurse and compose --- *)
  destruct (zr_copy_frame q) as [HF _].
  destruct (HF q' EC)
    as (HRet & HIn & HOut & HLast & HWrap & HWsz & HWh & HSn & HFl
        & HCk & HTo).
  assert (Hentry' : zr_copy_entry q').
  { unfold zr_copy_entry.
    split; [exact HWf'|].
    split; [rewrite HPut'; lia|].
    split; [rewrite HLeft'; lia|].
    split; [rewrite HLen'; lia|].
    rewrite HMode; exact Hm. }
  assert (Hn' : (Z.to_nat (u_length (s_cur (q_st q'))) <= n)%nat)
    by (rewrite HLen'; lia).
  destruct (IH c q' Hn' Hentry') as [AG | EX].
  - (* agreement composes *)
    left.
    destruct AG as (k & q'' & HI & HBt2 & HH2 & HB2 & HW2 & HS2 & HP2
                    & HSum2 & HOl2 & HM2 & HL2 & HR2 & HIn2 & HOut2
                    & HWr2 & HWs2 & HWh2 & HSn2 & HFl2 & HCk2 & HTo2).
    set (lenq := u_length (s_cur (q_st q))) in *.
    set (A := map (fun m => br_in (q_br q) (br_next (q_br q) + Z.of_nat m))
                  (seq 0 (Z.to_nat c2))) in *.
    set (B := map (fun m => br_in (q_br q') (br_next (q_br q') + Z.of_nat m))
                  (seq 0 (Z.to_nat (u_length (s_cur (q_st q')))))) in *.
    set (P := map (fun m => br_in (q_br q) (br_next (q_br q) + Z.of_nat m))
                  (seq 0 (Z.to_nat lenq))) in *.
    assert (HAB : br_bytes (q_br q) = (A ++ B) ++ br_bytes (q_br q''))
      by (rewrite HBytes, HBt2; now rewrite app_assoc).
    assert (HlenAB : length (A ++ B) = Z.to_nat lenq).
    { rewrite length_app. unfold A, B.
      rewrite !zr_mapseq_len, HLen'. unfold lenq. lia. }
    assert (Hlenhave : lenq <= br_have (q_br q)).
    { pose proof (br_bytes_length (q_br q)) as HhaveN.
      assert (HLL : length (br_bytes (q_br q))
              = (length (A ++ B) + length (br_bytes (q_br q'')))%nat)
        by (rewrite HAB; apply length_app).
      rewrite HhaveN, HlenAB in HLL. unfold lenq in *. lia. }
    assert (HP : br_bytes (q_br q)
                 = P ++ map (fun m => br_in (q_br q)
                              (br_next (q_br q) + lenq + Z.of_nat m))
                        (seq 0 (Z.to_nat (br_have (q_br q) - lenq)))).
    { unfold br_bytes at 1. unfold P.
      apply (zr_bytes_split (br_in (q_br q)) (br_have (q_br q))
               (br_next (q_br q)) lenq).
      unfold lenq in *. lia. }
    assert (HABP : A ++ B = P).
    { destruct (zr_app_inj (A ++ B) P
                  (br_bytes (q_br q''))
                  (map (fun m => br_in (q_br q)
                         (br_next (q_br q) + lenq + Z.of_nat m))
                       (seq 0 (Z.to_nat (br_have (q_br q) - lenq))))
                  ltac:(rewrite HlenAB; unfold P;
                        now rewrite zr_mapseq_len)
                  ltac:(rewrite <- HAB; exact HP)) as [HH _].
      exact HH. }
    exists (1 + k)%nat, q''.
    split.
    { rewrite (inf_iter14_add 1 k c q q'); [ exact HI |].
      apply inf_iter14_one. rewrite (zr_step_at_copy14 c q Hm). exact EC. }
    split.
    { rewrite HAB, HABP. reflexivity. }
    split. { now rewrite HH2, HHold. }
    split. { now rewrite HB2, HBits. }
    split. { exact HW2. }
    split.
    { rewrite HS2, HSlice, <- app_assoc, HABP. reflexivity. }
    split. { rewrite HP2, HPut', HLen'. unfold lenq. lia. }
    split. { rewrite HSum2, HPut', HLeft'. lia. }
    split. { exact HOl2. }
    split. { exact HM2. }
    split. { now rewrite HL2, HLast. }
    split. { now rewrite HR2, HRet. }
    split. { now rewrite HIn2, HIn. }
    split. { now rewrite HOut2, HOut. }
    split. { now rewrite HWr2, HWrap. }
    split. { now rewrite HWs2, HWsz. }
    split. { now rewrite HWh2, HWh. }
    split. { now rewrite HSn2, HSn. }
    split. { now rewrite HFl2, HFl. }
    split. { now rewrite HCk2, HCk. }
    { now rewrite HTo2, HTo. }
  - (* absorbed exit composes through the first step *)
    right.
    destruct EX as (m & sx & HLp & HMatch).
    exists (1 + m)%nat, sx.
    split.
    { apply (inf_loop14_after_iter 1 c q q');
        [ apply inf_iter14_one; rewrite (zr_step_at_copy14 c q Hm); exact EC
        | exact HLp ]. }
    { destruct sx as [qx|qx|qx r| |mx]; try exact HMatch; try contradiction.
      rewrite HMatch. exact HRet. }
Qed.

(* ==========================================================================
   4.  Frame/dispatch plumbing for the walk: TYPEDO preserves [h_wrap]
       (the ONLY writer of [h_wrap] is [set_wrap], whose lone call site is
       [inflateReset2] -- initialisation, not the step loop; so every arm
       is a reflexivity leaf), the M_STORED dispatch, and first-step
       aliasing (two states whose next step is THE SAME step function
       value share every iterate/loop of positive index).
   ========================================================================== *)


(** Reader-side companions (amendment #10): [br_haligned] vacuity at a
    drained hold, and its preservation through the TYPEDO reads on the
    walk's [h_last = 0] path. *)


(* ==========================================================================
   5.  The stored BLOCK TRIP: from the post-TYPEDO [M_STORED] dispatch
       state, the machine trip IS [decode_stored] on the same stream (the
       header via [zr_stored_sound], the payload via [zr_copy_loop] and
       the [read_bytes]/[bytes_bits] bridge), or an absorbed arm.  Exit
       arms mirror [zr_huff_exit] so the walk composes all three block
       kinds uniformly.
   ========================================================================== *)

Lemma zr_stored_trip14 : forall c q,
  zr_cflush_ok c ->
  br_wf (q_br q) ->
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  h_mode (s_hdr (q_st q)) = M_STORED ->
  (exists k q' payload,
     inf_iter14 k c q = Some q'
     /\ decode_stored (br_stream (q_br q))
        = Some (payload, br_stream (q_br q'))
     /\ br_wf (q_br q')
     /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
        = ob_slice (q_ob q) 0 (o_put (q_ob q)) ++ payload
     /\ o_put (q_ob q') + o_left (q_ob q')
        = o_put (q_ob q) + o_left (q_ob q)
     /\ 0 <= o_put (q_ob q')
     /\ 0 <= o_left (q_ob q')
     /\ h_mode (s_hdr (q_st q')) = M_TYPE
     /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
     /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
     /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q))
     /\ w_whave (s_win (q_st q')) = w_whave (s_win (q_st q))
     /\ t_sane (s_tab (q_st q')) = t_sane (s_tab (q_st q))
     /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
     (* amendment #11: h_check/h_total frame conjuncts — carrier
        q7-decode; g1 census; q6 pre-ruling;
        #10 shape *)
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
     /\ W2Stream.br_haligned (q_br q'))
  \/ (exists k q',
       inf_iter14 k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD)
  \/ (exists n s,
       inf_loop14 n c q = Some s
       /\ match s with
          | InfLeave q2 => q_ret q2 = q_ret q
          | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
          | InfFuel => True
          end).
Proof.
  intros c q Hc Hwf Hput Hleft Hm.
  assert (HF : n_flush c <> Z_TREES) by (destruct Hc as [_ HT]; exact HT).
  destruct (zr_stored_sound c q HF Hwf)
    as [ (b & ES)
       | [ (b & ES)
         | (b & len & r1 & R1 & R2 & Hlen & Hwfb & Hb0 & EARM) ] ].
  - (* starved leave: ret untouched *)
    right; right. exists 1%nat, (InfLeave (qset_br q b)).
    split.
    { apply inf_loop14_one_exit;
        [ rewrite (zr_step_at_stored14 c q Hm); exact ES | exact I ]. }
    reflexivity.
  - (* failed complement check: one continuing step into M_BAD *)
    right; left. exists 1%nat, (qbad (qset_br q b) MSG_STORED_LEN).
    split.
    { apply inf_iter14_one. rewrite (zr_step_at_stored14 c q Hm). exact ES. }
    reflexivity.
  - (* the transfer: header agreed, payload via the copy loop *)
    set (q1 := qmode (qset_br (qset_st q (set_length (q_st q) len))
                        (br_initbits b)) M_COPY_) in *.
    set (q2 := qmode q1 M_COPY).
    assert (Hm2 : h_mode (s_hdr (q_st q2)) = M_COPY) by reflexivity.
    assert (HSTEP : inf_step14 c q = inf_step14 c q2).
    { rewrite (zr_step_at_stored14 c q Hm), EARM,
        (zr_step_at_copy14 c q2 Hm2).
      unfold inf_COPY_. reflexivity. }
    assert (Hentry2 : zr_copy_entry q2).
    { unfold zr_copy_entry.
      split; [exact Hwfb|].
      split; [exact Hput|].
      split; [exact Hleft|].
      split; [exact Hlen|].
      exact Hm2. }
    destruct (zr_copy_loop14 (Z.to_nat (u_length (s_cur (q_st q2)))) c q2
                (Nat.le_refl _) Hentry2) as [AG | EX].
    + (* agreement: identify the trip with decode_stored *)
      destruct AG as (k & q3 & HI & HBytes & HHold & HBits & HWf3 & HSlice
                      & HPut3 & HSum3 & HOl3 & HM3 & HL3 & HR3 & HIn3
                      & HOut3 & HWr3 & HWs3 & HWh3 & HSn3 & HFl3c
                      & HCk3c & HTo3c).
      destruct k as [|k'].
      { exfalso. cbn [inf_iter14] in HI. injection HI as <-.
        rewrite Hm2 in HM3. discriminate. }
      left. exists (S k'), q3.
      exists (map (fun m => br_in (q_br q2) (br_next (q_br q2) + Z.of_nat m))
                  (seq 0 (Z.to_nat (u_length (s_cur (q_st q2)))))).
      split. { exact (inf_iter14_alias_S c q q2 k' q3 HSTEP HI). }
      split.
      { unfold decode_stored.
        rewrite R1. cbv beta iota.
        rewrite R2. cbv beta iota.
        rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l, Z.eqb_refl.
        cbv beta iota.
        assert (HS1 : br_stream (br_initbits b)
                      = bytes_bits (br_bytes (q_br q2))).
        { unfold br_stream. rewrite Hb0, zwrite_0. reflexivity. }
        assert (HB3 : br_bits (q_br q3) = 0)
          by (rewrite HBits; exact Hb0).
        assert (HS3 : br_stream (q_br q3)
                      = bytes_bits (br_bytes (q_br q3))).
        { unfold br_stream. rewrite HB3, zwrite_0. reflexivity. }
        rewrite HS1, HS3, HBytes, bytes_bits_app.
        set (MAP := map (fun m => br_in (q_br q2)
                           (br_next (q_br q2) + Z.of_nat m))
                        (seq 0 (Z.to_nat (u_length (s_cur (q_st q2)))))).
        replace (Z.to_nat len) with (length MAP)
          by (unfold MAP; rewrite zr_mapseq_len; reflexivity).
        rewrite read_bytes_bytes_bits.
        rewrite stored_map_u8_id; [reflexivity|].
        apply Forall_forall. intros y Hy.
        apply in_map_iff in Hy. destruct Hy as (m & Hme & _).
        rewrite <- Hme.
        destruct Hwfb as (_ & _ & _ & Hr4). exact (Hr4 _). }
      split. { exact HWf3. }
      split. { exact HSlice. }
      split. { exact HSum3. }
      split.
      { rewrite HPut3.
        change (o_put (q_ob q2)) with (o_put (q_ob q)).
        change (u_length (s_cur (q_st q2))) with len.
        lia. }
      split. { exact HOl3. }
      split. { exact HM3. }
      split. { exact HL3. }
      split. { exact HR3. }
      split. { exact HIn3. }
      split. { exact HOut3. }
      split. { exact HWr3. }
      split. { exact HWs3. }
      split. { exact HWh3. }
      split. { exact HSn3. }
      split. { rewrite HFl3c. reflexivity. }
      split. { rewrite HCk3c. reflexivity. }
      split. { rewrite HTo3c. reflexivity. }
      apply zr_haligned0. rewrite HBits. exact Hb0.
    + (* absorbed exit transfers through the shared first step *)
      right; right.
      destruct EX as (n & s & HL & HMatch).
      destruct n as [|n']; [cbn [inf_loop14] in HL; discriminate|].
      exists (S n'), s.
      split. { exact (inf_loop14_alias_S c q q2 n' s HSTEP HL). }
      destruct s as [qx|qx|qx r| |]; exact HMatch.
Qed.

(* ==========================================================================
   6.  THE BODY WALK.  Wrap-agnostic; hypothesized on the two huffman
       residues; two entries (M_TYPE; wrap-0 M_HEAD via the delegated
       TYPEDO).  The agreement arm IS [dec_stream_from] on the entry
       stream at the entry output slice (general-acc form; at the face
       assemblies' entry states [o_put = 0] gives [dec_stream_rem]).
   ========================================================================== *)


Definition zr_body_exit14 (c : InfCtx) (q : InfSt) : Prop :=
  (exists k q' out,
     inf_iter14 k c q = Some q'
     /\ dec_stream_from (br_stream (q_br q))
          (ob_slice (q_ob q) 0 (o_put (q_ob q)))
        = Some (out, br_stream (q_br q'))
     /\ ob_slice (q_ob q') 0 (o_put (q_ob q')) = out
     /\ br_wf (q_br q')
     /\ 0 <= o_put (q_ob q')
     /\ 0 <= o_left (q_ob q')
     /\ o_put (q_ob q') + o_left (q_ob q')
        = o_put (q_ob q) + o_left (q_ob q)
     /\ h_mode (s_hdr (q_st q')) = M_TYPE
     /\ h_last (s_hdr (q_st q')) <> 0
     /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
     /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
     (* amendment #11: h_check/h_total frame conjuncts — carrier
        q7-decode; g1 census; q6 pre-ruling;
        #10 shape *)
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
     /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q))
     /\ w_whave (s_win (q_st q')) = w_whave (s_win (q_st q))
     /\ t_sane (s_tab (q_st q')) = t_sane (s_tab (q_st q))
     /\ W2Stream.br_haligned (q_br q')
     /\ br_have (q_br q') + br_bits (q_br q') / 8 <= 4294967290)
  \/ (exists k q',
      inf_iter14 k c q = Some q' /\ h_mode (s_hdr (q_st q')) = M_BAD)
  \/ (exists n s,
      inf_loop14 n c q = Some s
      /\ match s with
         | InfLeave q2 => q_ret q2 = q_ret q
         | InfCont _ => False | InfRet _ _ => False | InfDead _ => False
         | InfFuel => True
         end).

(** One block landed at [q3] with its [dec_blk] equation assembled:
    close the walk — exit if the block was final, recurse otherwise. *)
Lemma zr_body_tail14 : forall n' c q k13 lastb q3,
  (forall q0,
      (length (br_stream (q_br q0)) < n')%nat ->
      zr_body_entry q0 ->
      h_mode (s_hdr (q_st q0)) = M_TYPE ->
      zr_body_exit14 c q0) ->
  (length (br_stream (q_br q)) <= n')%nat ->
  0 <= lastb < 2 ->
  br_wf (q_br q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  q_ret q = 0 ->
  br_have (q_br q) + br_bits (q_br q) / 8 <= 4294967290 ->
  inf_iter14 k13 c q = Some q3 ->
  dec_blk (br_stream (q_br q)) (ob_slice (q_ob q) 0 (o_put (q_ob q)))
    = Some (Z.eqb lastb 1,
            ob_slice (q_ob q3) 0 (o_put (q_ob q3)),
            br_stream (q_br q3)) ->
  br_wf (q_br q3) ->
  0 <= o_put (q_ob q3) ->
  0 <= o_left (q_ob q3) ->
  o_put (q_ob q3) + o_left (q_ob q3) = o_put (q_ob q) + o_left (q_ob q) ->
  h_mode (s_hdr (q_st q3)) = M_TYPE ->
  h_last (s_hdr (q_st q3)) = lastb ->
  q_ret q3 = q_ret q -> q_in q3 = q_in q -> q_out q3 = q_out q ->
  h_wrap (s_hdr (q_st q3)) = h_wrap (s_hdr (q_st q)) ->
  w_wsize (s_win (q_st q3)) = w_wsize (s_win (q_st q)) ->
  w_whave (s_win (q_st q3)) = w_whave (s_win (q_st q)) ->
  t_sane (s_tab (q_st q3)) = t_sane (s_tab (q_st q)) ->
  h_flags (s_hdr (q_st q3)) = h_flags (s_hdr (q_st q)) ->
  (* amendment #11: h_check/h_total frame conjuncts — carrier q7-decode;
     g1 census; q6 pre-ruling; #10 shape *)
  h_check (s_hdr (q_st q3)) = h_check (s_hdr (q_st q)) ->
  h_total (s_hdr (q_st q3)) = h_total (s_hdr (q_st q)) ->
  W2Stream.br_haligned (q_br q3) ->
  zr_body_exit14 c q.
Proof.
  intros n' c q k13 lastb q3 IH Hn Hlb Hwf0 Htie Hcap Hwh0 Hsn0 Hrt0
         Hbud0 HI13 Hdec Hwf3 Hput3 Hleft3 Hsum3 Hm3 Hl3 Hret3 Hin3 Hout3
         Hwr3 Hws3 Hwh3 Hsn3 Hfl3 Hck3 Hto3 Hha3.
  pose proof (dec_blk_shorter _ _ _ _ _ Hdec) as Hshort.
  assert (Hbud3d : br_have (q_br q3) + br_bits (q_br q3) / 8
                   <= 4294967290).
  { pose proof (br_budget_mono (q_br q) (q_br q3) Hwf0 Hwf3
                  ltac:(lia)) as HBM. lia. }
  destruct (Z.eqb_spec lastb 1) as [E|N].
  - (* final block: the walk exits here *)
    left. exists k13, q3, (ob_slice (q_ob q3) 0 (o_put (q_ob q3))).
    split. { exact HI13. }
    split.
    { rewrite dec_stream_from_unfold, Hdec. cbv beta iota. reflexivity. }
    split. { reflexivity. }
    split. { exact Hwf3. }
    split. { exact Hput3. }
    split. { exact Hleft3. }
    split. { exact Hsum3. }
    split. { exact Hm3. }
    split. { rewrite Hl3, E. discriminate. }
    split. { exact Hret3. }
    split. { exact Hin3. }
    split. { exact Hout3. }
    split. { exact Hwr3. }
    split. { exact Hfl3. }
    split. { exact Hck3. }
    split. { exact Hto3. }
    split. { exact Hws3. }
    split. { exact Hwh3. }
    split. { exact Hsn3. }
    split. { exact Hha3. }
    exact Hbud3d.
  - (* non-final: recurse at q3 *)
    assert (E0 : lastb = 0) by lia.
    assert (Hentry3 : zr_body_entry q3).
    { split; [exact Hwf3|]. split; [exact Hput3|]. split; [exact Hleft3|].
      split; [rewrite Hout3, Hsum3; exact Htie|].
      split; [rewrite Hout3; exact Hcap|].
      split; [rewrite Hwh3; exact Hwh0|].
      split; [rewrite Hsn3; exact Hsn0|].
      split; [rewrite Hret3; exact Hrt0|].
      split; [rewrite Hl3; exact E0|].
      split; [exact Hha3|].
      exact Hbud3d. }
    destruct (IH q3 ltac:(lia) Hentry3 Hm3) as [AG | [BAD | EX]].
    + left.
      destruct AG as (k2 & q4 & out2 & HI2 & HD2 & HS4 & Hwf4 & Hput4
                      & Hleft4 & Hsum4 & Hm4 & Hl4 & Hret4 & Hin4 & Hout4
                      & Hwr4 & Hfl4 & Hck4 & Hto4 & Hws4 & Hwh4 & Hsn4
                      & Hha4 & Hbud4).
      exists (k13 + k2)%nat, q4, out2.
      split.
      { rewrite (inf_iter14_add k13 k2 c q q3 HI13). exact HI2. }
      split.
      { rewrite dec_stream_from_unfold, Hdec. cbv beta iota. exact HD2. }
      split. { exact HS4. }
      split. { exact Hwf4. }
      split. { exact Hput4. }
      split. { exact Hleft4. }
      split. { rewrite Hsum4. exact Hsum3. }
      split. { exact Hm4. }
      split. { exact Hl4. }
      split. { rewrite Hret4. exact Hret3. }
      split. { rewrite Hin4. exact Hin3. }
      split. { rewrite Hout4. exact Hout3. }
      split. { rewrite Hwr4. exact Hwr3. }
      split. { rewrite Hfl4. exact Hfl3. }
      split. { rewrite Hck4. exact Hck3. }
      split. { rewrite Hto4. exact Hto3. }
      split. { rewrite Hws4. exact Hws3. }
      split. { rewrite Hwh4. exact Hwh3. }
      split. { rewrite Hsn4. exact Hsn3. }
      split. { exact Hha4. }
      exact Hbud4.
    + right; left.
      destruct BAD as (k2 & q4 & HI2 & HM4).
      exists (k13 + k2)%nat, q4.
      split; [ rewrite (inf_iter14_add k13 k2 c q q3 HI13); exact HI2
             | exact HM4 ].
    + right; right.
      destruct EX as (n2 & s & HL2 & HMt).
      exists (k13 + n2)%nat, s.
      split; [ exact (inf_loop14_after_iter k13 c q q3 n2 s HI13 HL2) |].
      destruct s as [qx|qx|qx r| |]; try exact HMt.
      rewrite HMt. exact Hret3.
Qed.

(** One S-case of the walk, parameterised by the TYPEDO source [qsrc] so
    the two entries share it: [qsrc = q] at M_TYPE, [qmode q M_TYPEDO]
    at wrap-0 M_HEAD (the equation premises are reflexivity at both). *)
Lemma zr_body_blocks14 : forall n' c q qsrc,
  ZrHuffFixedLeg14 -> ZrHuffDynLeg14 -> zr_cflush_ok c ->
  (forall q0,
      (length (br_stream (q_br q0)) < n')%nat ->
      zr_body_entry q0 ->
      h_mode (s_hdr (q_st q0)) = M_TYPE ->
      zr_body_exit14 c q0) ->
  (length (br_stream (q_br q)) <= n')%nat ->
  br_wf (q_br q) ->
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  q_ret q = 0 ->
  W2Stream.br_haligned (q_br q) ->
  br_have (q_br q) + br_bits (q_br q) / 8 <= 4294967290 ->
  inf_step14 c q = inf_TYPEDO c qsrc ->
  q_br qsrc = q_br q ->
  q_ob qsrc = q_ob q ->
  q_ret qsrc = q_ret q ->
  q_in qsrc = q_in q ->
  q_out qsrc = q_out q ->
  h_last (s_hdr (q_st qsrc)) = 0 ->
  h_wrap (s_hdr (q_st qsrc)) = h_wrap (s_hdr (q_st q)) ->
  w_wsize (s_win (q_st qsrc)) = w_wsize (s_win (q_st q)) ->
  w_whave (s_win (q_st qsrc)) = w_whave (s_win (q_st q)) ->
  t_sane (s_tab (q_st qsrc)) = t_sane (s_tab (q_st q)) ->
  h_flags (s_hdr (q_st qsrc)) = h_flags (s_hdr (q_st q)) ->
  (* amendment #11: h_check/h_total frame conjuncts — carrier q7-decode;
     g1 census; q6 pre-ruling; #10 shape *)
  h_check (s_hdr (q_st qsrc)) = h_check (s_hdr (q_st q)) ->
  h_total (s_hdr (q_st qsrc)) = h_total (s_hdr (q_st q)) ->
  zr_body_exit14 c q.
Proof.
  intros n' c q qsrc HFix HDyn Hc IH Hn Hwf Hput Hleft Htie Hcap Hwh Hsn
         Hrt0 Hha Hbud HSTEP Hbr Hob Hrt Hin Hout Hl0 Hwr Hws Hwhs Hsns
         Hfls Hcks Htos.
  assert (HFl : n_flush c <> Z_TREES) by (destruct Hc as [_ HT]; exact HT).
  assert (Hwfs : br_wf (q_br qsrc)) by (rewrite Hbr; exact Hwf).
  destruct (zr_typedo_cases c qsrc HFl Hl0)
    as [(q1 & ET) | (q2 & ET & ERet)].
  2:{ (* header starvation leave *)
    right; right. exists 1%nat, (InfLeave q2).
    split.
    { apply inf_loop14_one_exit; [ rewrite HSTEP; exact ET | exact I ]. }
    rewrite ERet. exact Hrt. }
  assert (HI1 : inf_iter14 1 c q = Some q1)
    by (apply inf_iter14_one; rewrite HSTEP; exact ET).
  destruct (zr_typedo_sound c qsrc q1 HFl Hl0 Hwfs ET)
    as [HBad | (lastb & ty & r1 & R1 & R2 & HLast1 & Hwf1 & HFrame1 & HArm)].
  { (* reserved block type: M_BAD *)
    right; left. exists 1%nat, q1. split; [exact HI1 | exact HBad]. }
  rewrite Hbr in R1.
  destruct HFrame1 as (HOb1 & HIn1 & HOut1 & HRet1 & HWs1).
  rewrite Hob in HOb1. rewrite Hin in HIn1. rewrite Hout in HOut1.
  rewrite Hrt in HRet1. rewrite Hws in HWs1.
  destruct (zr_typedo_ride c qsrc q1 ET)
    as (HWr1 & HWh1 & HSn1 & HFl1 & HCk1 & HTo1).
  rewrite Hwr in HWr1. rewrite Hwhs in HWh1. rewrite Hsns in HSn1.
  rewrite Hfls in HFl1. rewrite Hcks in HCk1. rewrite Htos in HTo1.
  assert (Hhas : W2Stream.br_haligned (q_br qsrc))
    by (rewrite Hbr; exact Hha).
  assert (Hha1 : W2Stream.br_haligned (q_br q1))
    by (exact (zr_typedo_reader c qsrc q1 Hl0 Hwfs ET Hhas)).
  assert (HlenT : (length (br_stream (q_br q1))
                   <= length (br_stream (q_br q)))%nat).
  { eapply Nat.le_trans;
      [ exact (read_bits_le _ _ _ _ R2)
      | exact (read_bits_le _ _ _ _ R1) ]. }
  assert (Hbud1 : br_have (q_br q1) + br_bits (q_br q1) / 8
                  <= 4294967290).
  { pose proof (br_budget_mono (q_br q) (q_br q1) Hwf Hwf1 HlenT) as HBM.
    lia. }
  pose proof (read_bits_bound _ _ _ _ R1) as Hlb.
  change (2 ^ Z.of_nat 1) with 2 in Hlb.
  assert (Hput1 : 0 <= o_put (q_ob q1)) by (rewrite HOb1; exact Hput).
  assert (Hleft1 : 0 <= o_left (q_ob q1)) by (rewrite HOb1; exact Hleft).
  assert (Htie1 : q_out q1 = o_put (q_ob q1) + o_left (q_ob q1))
    by (rewrite HOut1, HOb1; exact Htie).
  assert (Hcap1 : q_out q1 <= 4294967295) by (rewrite HOut1; exact Hcap).
  assert (Hwh1 : w_whave (s_win (q_st q1)) = 0)
    by (rewrite HWh1; exact Hwh).
  assert (Hsn1 : t_sane (s_tab (q_st q1)) <> 0)
    by (rewrite HSn1; exact Hsn).
  assert (Hrt1 : q_ret q1 = 0) by (rewrite HRet1; exact Hrt0).
  destruct HArm as [ (Hty & Hm1)
                   | [ (Hty & Hm1 & HtL & HtLb & HtD & HtDb)
                     | (Hty & Hm1) ] ]; subst ty.
  - (* ---- stored block ---- *)
    destruct (zr_stored_trip14 c q1 Hc Hwf1 Hput1 Hleft1 Hm1)
      as [ (k1 & q3 & payload & HI3 & HDs & Hwf3 & HS3 & Hsum3 & Hput3
            & Hleft3 & Hm3 & Hl3 & Hret3 & Hin3 & Hout3 & Hwr3 & Hws3
            & Hwh3 & Hsn3 & Hfl3s & Hck3s & Hto3s & Hha3s)
         | [ (k1 & q3 & HI3 & HM3) | (n1 & s & HL1 & HMt) ] ].
    + apply (zr_body_tail14 n' c q (1 + k1)%nat lastb q3 IH Hn Hlb Hwf
               Htie Hcap Hwh Hsn Hrt0 Hbud).
      * rewrite (inf_iter14_add 1 k1 c q q1 HI1). exact HI3.
      * unfold dec_blk.
        rewrite R1. cbv beta iota.
        rewrite R2. cbv beta iota zeta.
        change (0 =? 0) with true. cbv beta iota.
        rewrite HDs. cbv beta iota.
        rewrite HS3, HOb1. reflexivity.
      * exact Hwf3.
      * exact Hput3.
      * exact Hleft3.
      * rewrite Hsum3, HOb1. reflexivity.
      * exact Hm3.
      * rewrite Hl3. exact HLast1.
      * rewrite Hret3. exact HRet1.
      * rewrite Hin3. exact HIn1.
      * rewrite Hout3. exact HOut1.
      * rewrite Hwr3. exact HWr1.
      * rewrite Hws3. exact HWs1.
      * rewrite Hwh3. exact HWh1.
      * rewrite Hsn3. exact HSn1.
      * rewrite Hfl3s. exact HFl1.
      * rewrite Hck3s. exact HCk1.
      * rewrite Hto3s. exact HTo1.
      * exact Hha3s.
    + right; left. exists (1 + k1)%nat, q3.
      split; [ rewrite (inf_iter14_add 1 k1 c q q1 HI1); exact HI3
             | exact HM3 ].
    + right; right. exists (1 + n1)%nat, s.
      split; [ exact (inf_loop14_after_iter 1 c q q1 n1 s HI1 HL1) |].
      destruct s as [qx|qx|qx r| |]; try exact HMt.
      rewrite HMt. exact HRet1.
  - (* ---- fixed huffman block ---- *)
    destruct (HFix c q1 Hc Hwf1 Hha1 Hbud1 Hput1 Hleft1 Htie1 Hcap1
                Hwh1 Hsn1 Hm1 HtL HtLb HtD HtDb)
      as [ (k1 & q3 & syms & r3 & HI3 & HDsym & HSt3 & Hwf3 & HRz & Hsum3
            & Hput3 & Hleft3 & Hm3 & Hl3 & HFr3 & Hha3r & Hbud3r)
         | [ (k1 & q3 & HI3 & HM3) | (n1 & s & HL1 & HMt) ] ].
    + destruct HFr3
        as (Hin3 & Hout3 & Hret3 & Hws3 & Hwr3 & Hfl3h & Hck3h & Hto3h
            & Hwh3 & Hsn3).
      apply (zr_body_tail14 n' c q (1 + k1)%nat lastb q3 IH Hn Hlb Hwf
               Htie Hcap Hwh Hsn Hrt0 Hbud).
      * rewrite (inf_iter14_add 1 k1 c q q1 HI1). exact HI3.
      * unfold dec_blk.
        rewrite R1. cbv beta iota.
        rewrite R2. cbv beta iota zeta.
        change (1 =? 0) with false. change (1 =? 1) with true.
        cbv beta iota.
        rewrite HDsym. cbv beta iota.
        rewrite HOb1 in HRz. rewrite HRz. cbv beta iota.
        rewrite HSt3. reflexivity.
      * exact Hwf3.
      * exact Hput3.
      * exact Hleft3.
      * rewrite Hsum3, HOb1. reflexivity.
      * exact Hm3.
      * rewrite Hl3. exact HLast1.
      * rewrite Hret3. exact HRet1.
      * rewrite Hin3. exact HIn1.
      * rewrite Hout3. exact HOut1.
      * rewrite Hwr3. exact HWr1.
      * rewrite Hws3. exact HWs1.
      * rewrite Hwh3. exact HWh1.
      * rewrite Hsn3. exact HSn1.
      * rewrite Hfl3h, HFl1. reflexivity.
      * rewrite Hck3h, HCk1. reflexivity.
      * rewrite Hto3h, HTo1. reflexivity.
      * exact Hha3r.
    + right; left. exists (1 + k1)%nat, q3.
      split; [ rewrite (inf_iter14_add 1 k1 c q q1 HI1); exact HI3
             | exact HM3 ].
    + right; right. exists (1 + n1)%nat, s.
      split; [ exact (inf_loop14_after_iter 1 c q q1 n1 s HI1 HL1) |].
      destruct s as [qx|qx|qx r| |]; try exact HMt.
      rewrite HMt. exact HRet1.
  - (* ---- dynamic huffman block ---- *)
    destruct (HDyn c q1 Hc Hwf1 Hha1 Hbud1 Hput1 Hleft1 Htie1 Hcap1
                Hwh1 Hsn1 Hrt1 Hm1)
      as [ (lit & dst & r3 & HDD & HEx)
         | [ (k1 & q3 & HI3 & HM3) | (n1 & s & HL1 & HMt) ] ].
    + destruct HEx
        as [ (k1 & q3 & syms & r4 & HI3 & HDsym & HSt3 & Hwf3 & HRz & Hsum3
              & Hput3 & Hleft3 & Hm3 & Hl3 & HFr3 & Hha3r & Hbud3r)
           | [ (k1 & q3 & HI3 & HM3) | (n1 & s & HL1 & HMt) ] ].
      * destruct HFr3
          as (Hin3 & Hout3 & Hret3 & Hws3 & Hwr3 & Hfl3h & Hck3h & Hto3h
              & Hwh3 & Hsn3).
        apply (zr_body_tail14 n' c q (1 + k1)%nat lastb q3 IH Hn Hlb Hwf
                 Htie Hcap Hwh Hsn Hrt0 Hbud).
        -- rewrite (inf_iter14_add 1 k1 c q q1 HI1). exact HI3.
        -- unfold dec_blk.
           rewrite R1. cbv beta iota.
           rewrite R2. cbv beta iota zeta.
           change (2 =? 0) with false. change (2 =? 1) with false.
           change (2 =? 2) with true. cbv beta iota.
           rewrite HDD. cbv beta iota.
           rewrite HDsym. cbv beta iota.
           rewrite HOb1 in HRz. rewrite HRz. cbv beta iota.
           rewrite HSt3. reflexivity.
        -- exact Hwf3.
        -- exact Hput3.
        -- exact Hleft3.
        -- rewrite Hsum3, HOb1. reflexivity.
        -- exact Hm3.
        -- rewrite Hl3. exact HLast1.
        -- rewrite Hret3. exact HRet1.
        -- rewrite Hin3. exact HIn1.
        -- rewrite Hout3. exact HOut1.
        -- rewrite Hwr3. exact HWr1.
        -- rewrite Hws3. exact HWs1.
        -- rewrite Hwh3. exact HWh1.
        -- rewrite Hsn3. exact HSn1.
        -- rewrite Hfl3h, HFl1. reflexivity.
        -- rewrite Hck3h, HCk1. reflexivity.
        -- rewrite Hto3h, HTo1. reflexivity.
        -- exact Hha3r.
      * right; left. exists (1 + k1)%nat, q3.
        split; [ rewrite (inf_iter14_add 1 k1 c q q1 HI1); exact HI3
               | exact HM3 ].
      * right; right. exists (1 + n1)%nat, s.
        split; [ exact (inf_loop14_after_iter 1 c q q1 n1 s HI1 HL1) |].
        destruct s as [qx|qx|qx r| |]; try exact HMt.
        rewrite HMt. exact HRet1.
    + right; left. exists (1 + k1)%nat, q3.
      split; [ rewrite (inf_iter14_add 1 k1 c q q1 HI1); exact HI3
             | exact HM3 ].
    + right; right. exists (1 + n1)%nat, s.
      split; [ exact (inf_loop14_after_iter 1 c q q1 n1 s HI1 HL1) |].
      destruct s as [qx|qx|qx r| |]; try exact HMt.
      rewrite HMt. exact HRet1.
Qed.

Lemma zr_body_walk_fuel14 : forall n c q,
  ZrHuffFixedLeg14 -> ZrHuffDynLeg14 -> zr_cflush_ok c ->
  (length (br_stream (q_br q)) < n)%nat ->
  zr_body_entry q ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  zr_body_exit14 c q.
Proof.
  induction n as [|n' IHn]; intros c q HFix HDyn Hc Hn Hentry Hm;
    [lia|].
  destruct Hentry
    as (Hwf & Hput & Hleft & Htie & Hcap & Hwh & Hsn & Hrt0 & Hlast
        & Hha & Hbud).
  apply (zr_body_blocks14 n' c q q HFix HDyn Hc).
  - intros q0 Hf He0 Hm0. exact (IHn c q0 HFix HDyn Hc Hf He0 Hm0).
  - lia.
  - exact Hwf.
  - exact Hput.
  - exact Hleft.
  - exact Htie.
  - exact Hcap.
  - exact Hwh.
  - exact Hsn.
  - exact Hrt0.
  - exact Hha.
  - exact Hbud.
  - exact (zr_step_at_type14 c q Hc Hm).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hlast.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** THE WALK, entry 1: at a block boundary ([M_TYPE], not after the
    final block). *)

(** THE WALK, entry 2: the raw lane's fresh state ([M_HEAD] at wrap 0,
    where HEAD delegates straight to TYPEDO). *)

