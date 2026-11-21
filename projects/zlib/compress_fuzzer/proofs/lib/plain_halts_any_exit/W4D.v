(** * W4D — the if_loop fold + if_model classification at TWO-LEVEL
      tables (dyn round Leg A fast side, q7-decode, 2026-08-20,
      OFF-TREE SCRATCH).

    The dyn twin of the landed [W4Fold]: the fold body and the writeback
    layer are verbatim (they consume the trip's conclusion only); the
    ctx pack swaps root-only ownership for [zr_two_own_v3] + the landed
    pins + the population bounds, and the trip call becomes
    [W3D.w3d_trip].  All the finish/writeback machinery ([w4_wb],
    [w4_entry_pack], [w4_finish_*], [w4_haligned_vac], [w4_syms_prefix],
    [w4_resolve_single], [if_loop_S], [w4_post]) is REUSED from the
    landed W4Fold. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate InflateFast
  InflateThy ZBitsBridge DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W1Content W2Stream
  W3Trip W4Fold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6P.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1StmtsV3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W3D.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The per-call constants at two-level tables.
   ========================================================================== *)

Definition w4d_ctxpack (c : IfCtx) (rootL rootD : Z) (ll dl : list nat)
           (entl entd : nat -> Code) : Prop :=
  ValidLengths ll 15%nat /\ ValidLengths dl 15%nat
  /\ zr_two_own_v3 (f_lcode c) rootL ll entl
  /\ zr_two_own_v3 (f_dcode c) rootD dl entd
  /\ zr_len_ents ll entl /\ zr_dist_ents dl entd
  /\ (length ll <= 286)%nat /\ (length dl <= 30)%nat
  /\ 0 < rootL <= 15 /\ 0 < rootD <= 15
  /\ f_lmask c = Z.shiftl 1 rootL - 1
  /\ f_dmask c = Z.shiftl 1 rootD - 1
  /\ f_whave c = 0 /\ f_sane c <> 0 /\ if_inb c
  /\ f_end c <= 4294967295.

(* ==========================================================================
   2.  LAYER 1: the fold (body verbatim from W4Fold.w4_loop).
   ========================================================================== *)

Lemma w4d_loop :
  forall (n : nat) (c : IfCtx) (rootL rootD : Z) (ll dl : list nat)
         (entl entd : nat -> Code) (s : IfSt),
    w4d_ctxpack c rootL rootD ll dl entl entd ->
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
  pose proof Hpack as (HVl & HVd & HownL & HownD & Hle & Hde & Hpl & Hpd
                       & HrL & HrD & EmL & EmD & Hwh & Hsn & Hinb
                       & Hendcap).
  pose proof (w3d_trip c s rootL rootD ll dl entl entd HVl HVd HownL HownD
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
   3.  LAYER 2: the [if_model] classification (body verbatim from
       W4Fold.w4_if_model).
   ========================================================================== *)

Theorem w4d_if_model :
  forall (a : IfArgs) (b : BR) (rootL rootD : Z) (ll dl : list nat)
         (entl entd : nat -> Code),
    w4d_ctxpack (if_ctx a) rootL rootD ll dl entl entd ->
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
                       & _ & _ & Hinb & Hendcap).
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
  pose proof (w4d_loop (S (Z.to_nat (f_end c - f_out s0))) c rootL rootD
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

Print Assumptions w4d_loop.
Print Assumptions w4d_if_model.
