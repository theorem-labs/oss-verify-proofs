(** * W4Fold — the if_loop fold + if_model classification (q7-decode,
      ZrLenFastLeg discharge W4, 2026-08-20, OFF-TREE SCRATCH).

    Layer 1 ([w4_loop]): folding W3's per-trip classification over
    [if_loop] — the fast walk's exits carry a non-end symbol prefix with
    the [resolve_lz] slice threading.  Layer 2 ([w4_if_model]): the
    [if_model] classification through [if_finish]'s writeback, with the
    re-entry reader's stream/wf/alignment facts.  Stays on the
    Inflate/InflateFast layer — no reach-layer imports, so it survives
    StepReach/StepPres waves. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate InflateFast
  InflateThy ZBitsBridge DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W1Content W2Stream W3Trip.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Local copy of the scratch interface (re-point at landing).
   ========================================================================== *)

(** Copy of ZReproQ6Q.zr_syms_prefix (scratch; re-point at landing). *)
Fixpoint w4_syms_prefix (ll dl : list nat) (bits : list bool)
         (syms : list lz_sym) (rem : list bool) {struct syms} : Prop :=
  match syms with
  | [] => rem = bits
  | s :: tl =>
      s <> LzEnd
      /\ exists r1, decode_lit_len ll dl bits = Some (s, r1)
                    /\ w4_syms_prefix ll dl r1 tl rem
  end.

(** A single resolved symbol composes on the left of a resolve run. *)
Lemma w4_resolve_single : forall sy p acc acc1,
  sy <> LzEnd ->
  resolve_lz [sy] acc = Some acc1 ->
  resolve_lz (sy :: p) acc = resolve_lz p acc1.
Proof.
  intros sy p acc acc1 Hne H.
  destruct sy as [v|len dist|]; [| |congruence].
  - cbn [resolve_lz] in H |- *. injection H as <-. reflexivity.
  - cbn [resolve_lz] in H |- *.
    destruct ((dist =? 0)%nat || (length acc <? dist)%nat);
      [discriminate|].
    injection H as <-. reflexivity.
Qed.

(* ==========================================================================
   2.  The loop unfolding equation and the invariant packs.
   ========================================================================== *)

Lemma if_loop_S : forall n c s,
  if_loop (S n) c s = match if_step c s with
                      | IfCont s' => if_loop n c s'
                      | r => Some r
                      end.
Proof. reflexivity. Qed.

(** The per-call constants (W3's ctx premises + the out-end cap). *)
Definition w4_ctxpack (c : IfCtx) (rootL rootD : Z) (ll dl : list nat)
           (entl entd : nat -> Code) : Prop :=
  ValidLengths ll 15%nat /\ ValidLengths dl 15%nat
  /\ w3_root_own (f_lcode c) rootL ll 15%nat entl
  /\ w3_root_own (f_dcode c) rootD dl 15%nat entd
  /\ w3_len_ents ll entl /\ w3_dist_ents dl entd
  /\ 0 < rootL <= 15 /\ 0 < rootD <= 15
  /\ f_lmask c = Z.shiftl 1 rootL - 1
  /\ f_dmask c = Z.shiftl 1 rootD - 1
  /\ f_whave c = 0 /\ f_sane c <> 0 /\ if_inb c
  /\ f_end c <= 4294967295.

(** What every fold exit guarantees (absolute caps; composes with
    [w3_post]'s relative ones). *)
Definition w4_post (c : IfCtx) (s s' : IfSt) : Prop :=
  if_swf s' /\ if_haligned c s' /\ f_bits s' <= 60
  /\ f_in s <= f_in s' /\ f_out s <= f_out s'
  /\ f_in s' <= f_last c + 5
  /\ f_in s - f_bits s / 8 <= f_in s' - f_bits s' / 8
  /\ f_out s' <= f_end c + 257.

(* ==========================================================================
   3.  LAYER 1: the fold.
   ========================================================================== *)

Lemma w4_loop :
  forall (n : nat) (c : IfCtx) (rootL rootD : Z) (ll dl : list nat)
         (entl entd : nat -> Code) (s : IfSt),
    w4_ctxpack c rootL rootD ll dl entl entd ->
    if_swf s -> if_haligned c s -> f_bits s <= 60 ->
    f_in s + 6 <= f_last c + 5 ->
    0 <= f_beg c <= f_out s -> f_out s <= 4294967295 ->
    f_out s < f_end c ->
    match if_loop n c s with
    | Some (IfStop s') =>
        exists p rem,
          w4_syms_prefix ll dl (if_stream c s) p rem
          /\ p <> []
          /\ if_stream c s' = rem
          /\ (length rem < length (if_stream c s))%nat
          /\ resolve_lz p (zslice (f_buf s) 0 (f_out s))
             = Some (zslice (f_buf s') 0 (f_out s'))
          /\ w4_post c s s'
    | Some (IfEob s') =>
        exists p rem,
          w4_syms_prefix ll dl (if_stream c s) p rem
          /\ decode_lit_len ll dl rem = Some (LzEnd, if_stream c s')
          /\ resolve_lz p (zslice (f_buf s) 0 (f_out s))
             = Some (zslice (f_buf s') 0 (f_out s'))
          /\ w4_post c s s'
    | Some (IfBad s' m) => True
    | Some (IfCont s') => True
    | Some IfFuel => True
    | None => True
    end.
Proof.
  induction n as [|n IHn];
    intros c rootL rootD ll dl entl entd s Hpack Hswf Hal Hcap Hroom
           Hbeg Hocap Hoend;
    [exact I|].
  pose proof Hpack as (HVl & HVd & HownL & HownD & Hle & Hde & HrL & HrD
                       & EmL & EmD & Hwh & Hsn & Hinb & Hendcap).
  pose proof (w3_trip c s rootL rootD ll dl entl entd HVl HVd HownL HownD
                Hle Hde HrL HrD EmL EmD Hwh Hsn Hinb Hswf Hal Hcap Hroom
                Hbeg Hocap) as Htrip.
  rewrite if_loop_S.
  unfold if_step.
  destruct (if_body c s) as [s1|s1|s1 m|] eqn:EB;
    [| | exact I | exact I].
  - (* BodyOk: one non-end symbol consumed *)
    try rewrite EB in Htrip; cbv beta iota in Htrip.
    destruct Htrip as (sy & rest & Hdec & Hne & Hstr1 & Hres1 & Hpost1).
    pose proof Hpost1 as (Hsw1 & Hal1 & Hcap1 & Hinm1 & Houtm1
                          & Hincap1 & Hv1 & Houtc1).
    pose proof (decode_lit_len_shorter ll dl _ _ _ Hdec) as Hshort1.
    destruct (if_guard c s1) eqn:EG.
    + (* the guard holds: recurse *)
      unfold if_guard in EG. apply andb_prop in EG.
      destruct EG as (EGin & EGout).
      apply Z.ltb_lt in EGin. apply Z.ltb_lt in EGout.
      pose proof (IHn c rootL rootD ll dl entl entd s1 Hpack Hsw1 Hal1
                    Hcap1 ltac:(lia) ltac:(lia) ltac:(lia) EGout) as HIH.
      destruct (if_loop n c s1) as [[s'|s'|s'|s' m'|]|] eqn:EL1;
        [exact I| | |exact I|exact I|exact I].
      * (* IfStop below: cons the symbol onto the prefix *)
        try rewrite EL1 in HIH; cbv beta iota in HIH.
        destruct HIH as (p & rem' & Hpre & Hpne & Hstr' & Hlen' & Hres'
                         & Hpost').
        pose proof Hpost' as (Hsw' & Hal' & Hcap' & Hinm' & Houtm'
                              & Hincap' & Hv' & Houtc').
        rewrite Hstr1 in Hpre, Hlen'.
        exists (sy :: p), rem'.
        split.
        { cbn [w4_syms_prefix]. split; [exact Hne|].
          exists rest. split; [exact Hdec | exact Hpre]. }
        split; [discriminate|].
        split; [exact Hstr'|].
        split; [lia|].
        split.
        { rewrite (w4_resolve_single sy p _ _ Hne Hres1). exact Hres'. }
        split; [exact Hsw'|].
        split; [exact Hal'|].
        split; [exact Hcap'|].
        split; [lia|].
        split; [lia|].
        split; [exact Hincap'|].
        split; [lia|].
        exact Houtc'.
      * (* IfEob below: cons the symbol onto the prefix *)
        try rewrite EL1 in HIH; cbv beta iota in HIH.
        destruct HIH as (p & rem' & Hpre & Hend & Hres' & Hpost').
        pose proof Hpost' as (Hsw' & Hal' & Hcap' & Hinm' & Houtm'
                              & Hincap' & Hv' & Houtc').
        rewrite Hstr1 in Hpre.
        exists (sy :: p), rem'.
        split.
        { cbn [w4_syms_prefix]. split; [exact Hne|].
          exists rest. split; [exact Hdec | exact Hpre]. }
        split; [exact Hend|].
        split.
        { rewrite (w4_resolve_single sy p _ _ Hne Hres1). exact Hres'. }
        split; [exact Hsw'|].
        split; [exact Hal'|].
        split; [exact Hcap'|].
        split; [lia|].
        split; [lia|].
        split; [exact Hincap'|].
        split; [lia|].
        exact Houtc'.
    + (* the guard failed: stop with the singleton prefix *)
      exists [sy], rest.
      split.
      { cbn [w4_syms_prefix]. split; [exact Hne|].
        exists rest. split; [exact Hdec | reflexivity]. }
      split; [discriminate|].
      split; [exact Hstr1|].
      split; [exact Hshort1|].
      split; [exact Hres1|].
      split; [exact Hsw1|].
      split; [exact Hal1|].
      split; [exact Hcap1|].
      split; [exact Hinm1|].
      split; [exact Houtm1|].
      split; [exact Hincap1|].
      split; [exact Hv1|].
      lia.
  - (* BodyEob: the empty prefix, end-of-block decoded *)
    try rewrite EB in Htrip; cbv beta iota in Htrip.
    destruct Htrip as (Hdec & Hout1 & Hbuf1 & Hpost1).
    pose proof Hpost1 as (Hsw1 & Hal1 & Hcap1 & Hinm1 & Houtm1
                          & Hincap1 & Hv1 & Houtc1).
    exists [], (if_stream c s).
    split; [reflexivity|].
    split; [exact Hdec|].
    split.
    { cbn [resolve_lz]. rewrite Hbuf1, Hout1. reflexivity. }
    split; [exact Hsw1|].
    split; [exact Hal1|].
    split; [exact Hcap1|].
    split; [exact Hinm1|].
    split; [exact Houtm1|].
    split; [exact Hincap1|].
    split; [exact Hv1|].
    lia.
Qed.

(* ==========================================================================
   4.  [if_finish] projections beyond W2's block.
   ========================================================================== *)

Lemma w4_finish_bits : forall c s e,
  0 <= f_bits s <= 4294967295 ->
  y_bits (if_finish c s e) = f_bits s mod 8.
Proof.
  intros c s e Hb.
  unfold if_finish. cbn [y_bits].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (Z.shiftl_mul_pow2 (f_bits s / 8) 3) by lia.
  change (2 ^ 3) with 8.
  assert (Em : f_bits s - f_bits s / 8 * 8 = f_bits s mod 8)
    by (rewrite Z.mod_eq by lia; ring).
  rewrite Em.
  pose proof (Z.mod_pos_bound (f_bits s) 8 ltac:(lia)).
  apply u32_id. lia.
Qed.

Lemma w4_finish_availout : forall c s e,
  0 <= 257 + f_end c - f_out s <= 4294967295 ->
  y_avail_out (if_finish c s e) = 257 + f_end c - f_out s.
Proof.
  intros c s e H.
  unfold if_finish. cbn [y_avail_out].
  assert (E : (if Z.ltb (f_out s) (f_end c)
               then 257 + (f_end c - f_out s)
               else 257 - (f_out s - f_end c)) = 257 + f_end c - f_out s)
    by (destruct (Z.ltb (f_out s) (f_end c)); ring).
  rewrite E. apply u32_id. lia.
Qed.

(** A sub-byte reader is trivially aligned. *)
Lemma w4_haligned_vac : forall vb, 0 <= br_bits vb < 8 -> br_haligned vb.
Proof.
  intros vb Hb j Hj.
  exfalso.
  assert (E : br_bits vb / 8 = 0) by (apply Z.div_small; lia).
  lia.
Qed.

(** The writeback reader (Layer 2's re-entry record). *)
Definition w4_wb (c : IfCtx) (y : IfOut) : BR :=
  {| br_in := f_inbuf c; br_have := y_avail_in y; br_next := y_in y;
     br_hold := y_hold y; br_bits := y_bits y |}.

(* ==========================================================================
   5.  LAYER 2: the [if_model] classification.
   ========================================================================== *)

(** How [inf_LEN] fills the argument record from the machine's reader. *)
Definition w4_entry_pack (a : IfArgs) (b : BR) : Prop :=
  a_inbuf a = br_in b /\ a_next_in a = br_next b
  /\ a_avail_in a = br_have b /\ a_hold a = br_hold b
  /\ a_bits a = br_bits b.

Theorem w4_if_model :
  forall (a : IfArgs) (b : BR) (rootL rootD : Z) (ll dl : list nat)
         (entl entd : nat -> Code),
    w4_ctxpack (if_ctx a) rootL rootD ll dl entl entd ->
    w4_entry_pack a b ->
    br_wf b -> br_haligned b ->
    6 <= br_have b -> br_have b <= 4294967290 ->
    0 <= a_next_out a ->
    258 <= a_avail_out a ->
    a_next_out a + a_avail_out a <= 4294967295 ->
    a_start a = a_next_out a + a_avail_out a ->
    match if_model a with
    | Some y =>
        (y_exit y = ExLen ->
           exists p rem,
             w4_syms_prefix ll dl (br_stream b) p rem
             /\ p <> []
             /\ br_stream (w4_wb (if_ctx a) y) = rem
             /\ (length rem < length (br_stream b))%nat
             /\ resolve_lz p (zslice (a_buf a) 0 (a_next_out a))
                = Some (zslice (y_buf y) 0 (y_out y))
             /\ br_wf (w4_wb (if_ctx a) y)
             /\ br_haligned (w4_wb (if_ctx a) y)
             /\ a_next_out a <= y_out y
             /\ y_out y + y_avail_out y = a_next_out a + a_avail_out a)
        /\ (y_exit y = ExType ->
           exists p rem,
             w4_syms_prefix ll dl (br_stream b) p rem
             /\ decode_lit_len ll dl rem
                = Some (LzEnd, br_stream (w4_wb (if_ctx a) y))
             /\ resolve_lz p (zslice (a_buf a) 0 (a_next_out a))
                = Some (zslice (y_buf y) 0 (y_out y))
             /\ br_wf (w4_wb (if_ctx a) y)
             /\ br_haligned (w4_wb (if_ctx a) y)
             /\ a_next_out a <= y_out y
             /\ y_out y + y_avail_out y = a_next_out a + a_avail_out a)
        /\ (forall m, y_exit y = ExBad m -> True)
    | None => True
    end.
Proof.
  intros a b rootL rootD ll dl entl entd Hpack Hent Hwf Halb Hh6 Hhcap
         Hno0 Hav258 Hsumcap Hstart.
  pose proof Hent as (E1 & E2 & E3 & E4 & E5).
  pose proof Hwf as (Hwb & Hwh & Hwhave & Hwbytes).
  pose proof Hpack as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                       & Hinb & Hendcap).
  set (c := if_ctx a).
  set (s0 := if_st0 a).
  (* entry-state facts *)
  assert (Hstr0 : if_stream c s0 = br_stream b)
    by (apply w2_entry_stream; assumption).
  assert (Hsw0 : if_swf s0)
    by (apply (w2_entry_swf a b); [exact Hwf | exact E4 | exact E5]).
  assert (Hal0 : if_haligned c s0)
    by (apply (w2_entry_haligned a b); assumption).
  assert (Ebits0 : f_bits s0 = br_bits b)
    by (unfold s0; cbn [if_st0 f_bits]; exact E5).
  assert (Ein0 : f_in s0 = br_next b)
    by (unfold s0; cbn [if_st0 f_in]; exact E2).
  assert (Eout0 : f_out s0 = a_next_out a) by reflexivity.
  assert (Ebuf0 : f_buf s0 = a_buf a) by reflexivity.
  assert (Elast : f_last c = br_next b + (br_have b - 5))
    by (unfold c; cbn [if_ctx f_last]; rewrite E2, E3; reflexivity).
  assert (Eend : f_end c = a_next_out a + (a_avail_out a - 257))
    by reflexivity.
  assert (Ebeg : f_beg c = a_next_out a - (a_start a - a_avail_out a))
    by reflexivity.
  assert (Einbuf : f_inbuf c = br_in b)
    by (unfold c; cbn [if_ctx f_inbuf]; exact E1).
  (* the fold at the model's fuel *)
  pose proof (w4_loop (S (Z.to_nat (f_end c - f_out s0))) c rootL rootD
                ll dl entl entd s0 Hpack Hsw0 Hal0
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as HL.
  unfold if_model. cbv zeta.
  fold c. fold s0.
  destruct (if_loop (S (Z.to_nat (f_end c - f_out s0))) c s0)
    as [[s'|s'|s'|s' m|]|] eqn:EL;
    [exact I | | | | exact I | exact I].
  - (* IfStop -> ExLen *)
    try rewrite EL in HL; cbv beta iota in HL.
    destruct HL as (p & rem & Hpre & Hpne & Hstr' & Hlen' & Hres' & Hpost').
    pose proof Hpost' as (Hsw' & Hal' & Hcap' & Hinm' & Houtm'
                          & Hincap' & Hv' & Houtc').
    pose proof Hsw' as (Hb' & Hh' & _).
    (* division atoms *)
    assert (Hd0' : 0 <= f_bits s' / 8) by (apply Z.div_pos; lia).
    assert (Hd7' : f_bits s' / 8 <= 7).
    { pose proof (w3_div8_mono (f_bits s') 60 ltac:(lia)).
      assert (E60 : 60 / 8 = 7) by reflexivity. lia. }
    assert (Hd00 : 0 <= f_bits s0 / 8)
      by (apply Z.div_pos; lia).
    assert (Hd40 : f_bits s0 / 8 <= 4).
    { pose proof (w3_div8_mono (f_bits s0) 39 ltac:(lia)).
      assert (E39 : 39 / 8 = 4) by reflexivity. lia. }
    assert (Hav : 0 <= f_last c + 5 - (f_in s' - f_bits s' / 8)
                  <= 4294967295) by lia.
    pose proof (w2_finish_stream c s' ExLen Hinb Hsw' Hal'
                  ltac:(lia) ltac:(lia) Hav) as HFS.
    pose proof (w2_finish_br_wf c s' ExLen Hinb Hsw' ltac:(lia) Hav)
      as HFW.
    assert (HFB : y_bits (if_finish c s' ExLen) = f_bits s' mod 8)
      by (apply w4_finish_bits; lia).
    pose proof (Z.mod_pos_bound (f_bits s') 8 ltac:(lia)) as Hm8.
    assert (HAO : y_avail_out (if_finish c s' ExLen)
                  = 257 + f_end c - f_out s')
      by (apply w4_finish_availout; lia).
    split; [|split].
    + intros _.
      exists p, rem.
      rewrite Hstr0 in Hpre, Hlen'.
      split; [exact Hpre|].
      split; [exact Hpne|].
      split.
      { unfold w4_wb.
        change (br_stream
                  {| br_in := f_inbuf c;
                     br_have := y_avail_in (if_finish c s' ExLen);
                     br_next := y_in (if_finish c s' ExLen);
                     br_hold := y_hold (if_finish c s' ExLen);
                     br_bits := y_bits (if_finish c s' ExLen) |} = rem).
        rewrite HFS. exact Hstr'. }
      split; [exact Hlen'|].
      split.
      { rewrite w2_finish_buf, w2_finish_out.
        rewrite Ebuf0, Eout0 in Hres'. exact Hres'. }
      split.
      { unfold w4_wb. exact HFW. }
      split.
      { apply w4_haligned_vac. cbn [w4_wb br_bits]. rewrite HFB. lia. }
      split.
      { rewrite w2_finish_out. lia. }
      { rewrite w2_finish_out, HAO. lia. }
    + intros Hex. rewrite w2_finish_exit in Hex. discriminate.
    + intros m Hex. exact I.
  - (* IfEob -> ExType *)
    try rewrite EL in HL; cbv beta iota in HL.
    destruct HL as (p & rem & Hpre & Hend & Hres' & Hpost').
    pose proof Hpost' as (Hsw' & Hal' & Hcap' & Hinm' & Houtm'
                          & Hincap' & Hv' & Houtc').
    pose proof Hsw' as (Hb' & Hh' & _).
    assert (Hd0' : 0 <= f_bits s' / 8) by (apply Z.div_pos; lia).
    assert (Hd7' : f_bits s' / 8 <= 7).
    { pose proof (w3_div8_mono (f_bits s') 60 ltac:(lia)).
      assert (E60 : 60 / 8 = 7) by reflexivity. lia. }
    assert (Hd00 : 0 <= f_bits s0 / 8)
      by (apply Z.div_pos; lia).
    assert (Hd40 : f_bits s0 / 8 <= 4).
    { pose proof (w3_div8_mono (f_bits s0) 39 ltac:(lia)).
      assert (E39 : 39 / 8 = 4) by reflexivity. lia. }
    assert (Hav : 0 <= f_last c + 5 - (f_in s' - f_bits s' / 8)
                  <= 4294967295) by lia.
    pose proof (w2_finish_stream c s' ExType Hinb Hsw' Hal'
                  ltac:(lia) ltac:(lia) Hav) as HFS.
    pose proof (w2_finish_br_wf c s' ExType Hinb Hsw' ltac:(lia) Hav)
      as HFW.
    assert (HFB : y_bits (if_finish c s' ExType) = f_bits s' mod 8)
      by (apply w4_finish_bits; lia).
    pose proof (Z.mod_pos_bound (f_bits s') 8 ltac:(lia)) as Hm8.
    assert (HAO : y_avail_out (if_finish c s' ExType)
                  = 257 + f_end c - f_out s')
      by (apply w4_finish_availout; lia).
    split; [|split].
    + intros Hex. rewrite w2_finish_exit in Hex. discriminate.
    + intros _.
      exists p, rem.
      rewrite Hstr0 in Hpre.
      split; [exact Hpre|].
      split.
      { unfold w4_wb.
        change (decode_lit_len ll dl rem
                = Some (LzEnd,
                    br_stream
                      {| br_in := f_inbuf c;
                         br_have := y_avail_in (if_finish c s' ExType);
                         br_next := y_in (if_finish c s' ExType);
                         br_hold := y_hold (if_finish c s' ExType);
                         br_bits := y_bits (if_finish c s' ExType) |})).
        rewrite HFS. exact Hend. }
      split.
      { rewrite w2_finish_buf, w2_finish_out.
        rewrite Ebuf0, Eout0 in Hres'. exact Hres'. }
      split.
      { unfold w4_wb. exact HFW. }
      split.
      { apply w4_haligned_vac. cbn [w4_wb br_bits]. rewrite HFB. lia. }
      split.
      { rewrite w2_finish_out. lia. }
      { rewrite w2_finish_out, HAO. lia. }
    + intros m Hex. exact I.
  - (* IfBad -> ExBad *)
    split; [|split].
    + intros Hex. rewrite w2_finish_exit in Hex. discriminate.
    + intros Hex. rewrite w2_finish_exit in Hex. discriminate.
    + intros m' Hex. exact I.
Qed.

Print Assumptions w4_loop.
Print Assumptions w4_if_model.

(* ==========================================================================
   6.  THE REMAINING BRIDGE (deliberately NOT proved here — it re-derives
       against model-rt's RE-FROZEN ZrLenFastLeg, not against local
       copies).  Enumerated so the final discharge is assembly only:

   w4_len_fast_arm sketch, at an InfSt [q] with [h_mode = M_LEN] and the
   fast guard true (Z.leb 6 (br_have (q_br q)) && Z.leb 258 (o_left …)):

   (a) inf_LEN's fast branch builds the IfArgs record A(q)
       (Inflate.v:1074-1092).  [w4_entry_pack (A q) (q_br q)] holds by
       the w2_restore_* projections: a_inbuf/a_next_in/a_avail_in are
       br_in/br_next/br_have of the (restore-invariant) reader
       [w2_restore_br], and a_hold/a_bits are s_hold/s_bits of
       [q_restore q] = br_hold/br_bits of [q_br q]
       [w2_restore_hold/w2_restore_bits].
   (b) [w4_ctxpack (if_ctx (A q))] premises: f_lcode/f_dcode (A q) are
       the state's tbl_of views (definitional); rootL/rootD :=
       t_lenbits/t_distbits with the mask equations definitional from
       if_ctx; whave/sane from ZrLenFastLeg's premises; f_end cap from
       the q_out tie + cap.
   (c) [w4_if_model]'s premises map: 6 <= br_have (guard), avail_in cap
       (NEW ZrLenFastLeg premise, rc_inbud-tier), 258 <= o_left (guard),
       o_put + o_left = q_out <= 2^32-1 (the Prop's tie + cap, giving
       a_start = a_next_out + a_avail_out exactly).
   (d) On [if_model (A q) = Some y]: inf_LEN's writeback (q2 sets
       br_in := br_in b, br_have := y_avail_in, br_next := y_in with
       hold/bits STALE; st1 sets s_hold := y_hold, s_bits := y_bits;
       q_load pulls them into the reader) makes
       [q_br (q_load q4) = w4_wb (if_ctx (A q)) y] FIELD-BY-FIELD
       (w2_load_hold/bits/next/have/arr + E1), so w4_if_model's
       br_stream/br_wf/br_haligned conclusions ARE the CONT/ENDED arms'
       reader facts at q' := q5, with k = 1 (one inf_step: the whole
       fast call is a single InfCont).  y_exit dispatches the arm:
       ExLen -> CONT (q5 stays M_LEN), ExType -> ENDED (M_TYPE + the
       set_back -1), ExBad -> BAD.  The ob writeback (o_put := y_out,
       o_left := y_avail_out) turns the sum conservation into the
       Prop's o_put + o_left equation, and y_buf = f_buf s' feeds the
       resolve_lz conjunct.
   (e) On [if_model (A q) = None]: inf_LEN returns InfFuel; the Prop's
       fourth arm absorbs it via inf_loop with n = 1.
   ========================================================================== *)
