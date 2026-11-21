(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvDec InflateInvKit InflateInvFastA InflateInvFastB.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.


Section Loop.
  Variables (x : ffx) (s : inflate_state) (NI NO : Z).
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Hypothesis Xinb : forall i, 0 <= i < NI -> 0 <= arr_get (x_input x) i < 256.
  Hypothesis Xwinb : forall i, 0 <= i < arr_len (x_window x) -> 0 <= arr_get (x_window x) i < 256.
  Hypothesis Xbeg : x_beg x = 0.
  Hypothesis Xsane : x_sane x <> 0.
  Hypothesis Xwh : 0 <= x_whave x <= x_wsize x.
  Hypothesis Xwn : 0 <= x_wnext x <= x_wsize x.
  Hypothesis Xwlen : x_wsize x <> 0 -> arr_len (x_window x) = x_wsize x.
  Hypothesis Xws32 : x_wsize x < 2 ^ 32.
  Hypothesis Xlmask : x_lmask x = Z.ones (is_lenbits s).
  Hypothesis Xdmask : x_dmask x = Z.ones (is_distbits s).
  Variables extL extD : Z.
  Hypothesis TL : tab_ok LENS (fun i => code_at s (is_lencode s) i) (is_lenbits s) extL = true.
  Hypothesis TD : tab_ok DISTS (fun i => code_at s (is_distcode s) i) (is_distbits s) extD = true.
  Hypothesis Xlast : x_last x = NI - 5.
  Hypothesis Xend : x_end x = NO - 257.

  Definition fstep_fn (f : ffs) : ffs + (ffs * option (Z * option Z)) :=
    match fast_trip x s f with
    | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
    | FBreak f' mode msg => inr (f', Some (mode, msg))
    end.
  Definition lres (r : ffs + (ffs * option (Z * option Z))) : ffs * option (Z * option Z) :=
    match r with inl a => (a, None) | inr b => b end.
  Lemma fstep_fn_eq : forall f, fstep_fn f =
    match fast_trip x s f with
    | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
    | FBreak f' mode msg => inr (f', Some (mode, msg))
    end.
  Proof. reflexivity. Qed.

  Definition LPOST (i o b c : Z) (r : ffs + (ffs * option (Z * option Z))) : Prop :=
    let f' := fst (lres r) in
    FB f' /\ obytes NO (f_ob f') /\ o <= f_out f' <= NO /\ i <= f_in f' <= NI
    /\ 8 * f_in f' - f_bits f' >= 8 * i - b + c
    /\ match snd (lres r) with None => True | Some (md, _) => md = BAD \/ md = TYPE end.

  Lemma LPOST_w : forall i o b c i' o' b' c' r,
    LPOST i' o' b' c' r -> i <= i' -> o <= o' -> 8 * i' - b' + c' >= 8 * i - b + c -> LPOST i o b c r.
  Proof.
    intros i o b c i' o' b' c' r (A & B & C & D & E & F) H1 H2 H3. unfold LPOST.
    split; [exact A|]. split; [exact B|]. split; [lia|]. split; [lia|]. split; [lia | exact F].
  Qed.

  Lemma loop_spec0 : forall n f, FB f -> obytes NO (f_ob f) -> 0 <= f_in f -> f_in f + 6 <= NI -> 0 <= f_out f -> f_out f + 258 <= NO ->
    fast_loopN x s NO n f = true /\ LPOST (f_in f) (f_out f) (f_bits f) 0 (iterK_nat n fstep_fn f).
  Proof.
    induction n as [|n IH]; intros f Bf OB Hi0 Hi6 Ho0 Ho258.
    - cbn [fast_loopN iterK_nat]. split; [reflexivity|]. unfold LPOST, lres. cbn [fst snd].
      split; [exact Bf|]. split; [exact OB|]. repeat split; try lia.
    - cbn [fast_loopN iterK_nat].
      destruct f as [i o h b l d op fr ob]. rewrite (fstep_fn_eq (mkF i o h b l d op fr ob)). unfold FB in Bf. cbn [f_in f_out f_hold f_bits f_ob] in Bf, OB, Hi0, Hi6, Ho0, Ho258 |- *.
      destruct (trip_spec x s NI NO NO32 Xinb Xwinb Xbeg Xsane Xwh Xwn Xwlen Xws32 Xlmask Xdmask extL extD TL TD
                  i o h b l d op fr ob ltac:(lia) ltac:(lia) OB Hi0 Hi6 Ho0 Ho258) as (h1 & _ & _ & L1 & G & P).
      rewrite G. cbn [andb].
      destruct (fast_trip x s (mkF i o h b l d op fr ob)) as [f'|f' md msg].
      + unfold TPOST in P. cbn [fsf] in P. destruct P as (B' & OB' & O' & I' & C' & _).
        rewrite Xlast, Xend.
        destruct (Z.ltb_spec (f_in f') (NI - 5)); destruct (Z.ltb_spec (f_out f') (NO - 257)); cbn [andb].
        * destruct (IH f' B' OB' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [G' P'].
          split; [exact G'|]. eapply LPOST_w; [exact P' | lia | lia | lia].
        * split; [reflexivity|]. unfold LPOST, lres; cbn [fst snd]. split; [exact B'|]. split; [exact OB'|]. repeat split; lia.
        * split; [reflexivity|]. unfold LPOST, lres; cbn [fst snd]. split; [exact B'|]. split; [exact OB'|]. repeat split; lia.
        * split; [reflexivity|]. unfold LPOST, lres; cbn [fst snd]. split; [exact B'|]. split; [exact OB'|]. repeat split; lia.
      + split; [reflexivity|]. unfold TPOST in P. cbn [fsf] in P. destruct P as (B' & OB' & O' & I' & C' & M').
        unfold LPOST, lres; cbn [fst snd]. split; [exact B'|]. split; [exact OB'|]. repeat split; first [lia | exact M'].
  Qed.

  Lemma loop_spec : forall n i o h b l d op fr ob,
    0 <= b < 64 -> 0 <= h < 2 ^ b -> obytes NO ob -> 0 <= i -> i + 6 <= NI -> 0 <= o -> o + 258 <= NO ->
    let f := mkF i o h b l d op fr ob in
    exists h1, 0 <= h1 /\ h1 mod 2 ^ b = h /\ 1 <= lcons s h1 /\
      fast_loopN x s NO (S n) f = true /\ LPOST i o b (lcons s h1) (iterK_nat (S n) fstep_fn f).
  Proof.
    intros n i o h b l d op fr ob Bb Hh OB Hi0 Hi6 Ho0 Ho258. cbv zeta.
    cbn [fast_loopN iterK_nat]. rewrite (fstep_fn_eq (mkF i o h b l d op fr ob)).
    destruct (trip_spec x s NI NO NO32 Xinb Xwinb Xbeg Xsane Xwh Xwn Xwlen Xws32 Xlmask Xdmask extL extD TL TD
                i o h b l d op fr ob Bb Hh OB Hi0 Hi6 Ho0 Ho258) as (h1 & H1 & M1 & L1 & G & P).
    exists h1. split; [exact H1|]. split; [exact M1|]. split; [exact L1|].
    rewrite G. cbn [andb].
    destruct (fast_trip x s (mkF i o h b l d op fr ob)) as [f'|f' md msg].
    - unfold TPOST in P. cbn [fsf] in P. destruct P as (B' & OB' & O' & I' & C' & _).
      rewrite Xlast, Xend.
      destruct (Z.ltb_spec (f_in f') (NI - 5)); destruct (Z.ltb_spec (f_out f') (NO - 257)); cbn [andb].
      + destruct (loop_spec0 n f' B' OB' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [G' P'].
        split; [exact G'|]. eapply LPOST_w; [exact P' | lia | lia | lia].
      + split; [reflexivity|]. unfold LPOST, lres; cbn [fst snd]. split; [exact B'|]. split; [exact OB'|]. repeat split; lia.
      + split; [reflexivity|]. unfold LPOST, lres; cbn [fst snd]. split; [exact B'|]. split; [exact OB'|]. repeat split; lia.
      + split; [reflexivity|]. unfold LPOST, lres; cbn [fst snd]. split; [exact B'|]. split; [exact OB'|]. repeat split; lia.
    - split; [reflexivity|]. unfold TPOST in P. cbn [fsf] in P. destruct P as (B' & OB' & O' & I' & C' & M').
      unfold LPOST, lres; cbn [fst snd]. split; [exact B'|]. split; [exact OB'|]. repeat split; first [lia | exact M'].
  Qed.
End Loop.


Lemma avail_if : forall a e k, (if a <? e then k + (e - a) else k - (a - e)) = k + e - a.
Proof. intros a e k. destruct (a <? e); lia. Qed.

Lemma lcons_hb : forall s hv bv h, lcons (iset_bits (iset_hold s hv) bv) h = lcons s h.
Proof. intros [] hv bv h; reflexivity. Qed.
Lemma code_at_hb : forall s hv bv p i, code_at (iset_bits (iset_hold s hv) bv) p i = code_at s p i.
Proof. intros [] hv bv p i; reflexivity. Qed.

Lemma sinv_hb : forall s h b, sinv s -> sinv (iset_bits (iset_hold s h) b).
Proof.
  intros s h b SI. destruct s. unfold sinv, tables_ok, ctab_ok in *.
  cbn -[Z.shiftl tables_okf ctab_okf tab_ok arr_get arr_len codes_live order_a] in *. exact SI.
Qed.

Lemma plain_BAD : plain_mode BAD.
Proof. pose proof plain_modes as PM. decompose [and] PM; assumption. Qed.
Lemma plain_TYPE : plain_mode TYPE.
Proof. pose proof plain_modes as PM. decompose [and] PM; assumption. Qed.

Section Call.
  Variables (iv : ivariant) (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.
  Local Notation pinv := (pinv NI NO WN TOT0).

  Theorem fast_ok : forall w, pinv w -> is_mode (w_s w) = LEN -> fastcond iv (w_r w) = true -> DEBT w ->
    gFAST w = true /\ pinv (LOAD (inflate_fast (RESTORE w))) /\ ir_bits (w_r (LOAD (inflate_fast (RESTORE w)))) < 8
    /\ PHI (LOAD (inflate_fast (RESTORE w))) < PHI w.
  Proof.
    intros w PI Hm FC HD. dworld w. cbn [w_s is_mode] in Hm. unfold fastcond in FC. cbn [w_r ir_have ir_left] in FC.
    apply andb_prop in FC as [FC _]. (* 1.4: fastcond's bits < 8 conjunct, unused here *)
    apply andb_prop in FC as [FC FL]. apply andb_prop in FC as [_ FH]. apply Z.leb_le in FH. apply Z.leb_le in FL.
    unfold DEBT in HD. cbn [w_s w_r ir_bits ir_hold ir_next] in HD.
    pinv_open PI. subst f_mode. sinv_triage.
    destruct (dist_tab _ SIr eq_refl) as (extD & TD & HextD). cbn [is_codes is_distcode is_distbits] in TD, HextD.
    destruct (len_tab _ SIr eq_refl) as (extL & TL & HextL). cbn [is_codes is_lencode is_lenbits] in TL, HextL.
    destruct (tab_ok_root _ _ _ _ TL) as (Rl1 & _ & _). destruct (tab_ok_root _ _ _ _ TD) as (Rd1 & _ & _).
    assert (OL : r_out - r_left = r_put) by (destruct Xol as [X|[X1 X2]]; [exact X | exfalso; clear -X2 Klen Kcheck; lia]).
    unfold gFAST, ffG, ffx_of', ff0_of', ffuel, RESTORE, LOAD, inflate_fast. wred.
    rewrite (wrap32_id (r_have - 5)) by lia. rewrite (wrap32_id (r_left - 257)) by lia. rewrite OL. rewrite (wrap32_id r_put) by lia.
    rewrite Z.sub_diag. rewrite ClNO.
    rewrite iterZ_nat.
    match goal with |- context [fast_loopN ?X ?ST NO ?n ?F0] =>
      change (Z.to_nat (8 * r_have + r_left + 80)) with n;
      replace n with (S (Z.to_nat (8 * r_have + r_left + 79))) by liaq;
      set (XX := X); set (S1 := ST)
    end.
    change (fun f : ffs => match fast_trip XX S1 f with
                           | FCont f' => if (f_in f' <? x_last XX) && (f_out f' <? x_end XX) then inl f' else inr (f', None)
                           | FBreak f' mode msg => inr (f', Some (mode, msg)) end) with (fstep_fn XX S1).
    assert (XL : x_lmask XX = Z.ones f_lenbits) by (unfold XX; cbn [x_lmask]; rewrite zmask_ones by lia; f_equal; lia).
    assert (XD : x_dmask XX = Z.ones f_distbits) by (unfold XX; cbn [x_dmask]; rewrite zmask_ones by lia; f_equal; lia).
    assert (TL1 : tab_ok LENS (fun i => code_at S1 f_lencode i) f_lenbits extL = true).
    { apply (tab_ok_ext LENS (fun i => cat f_codes f_lencode i)); [intros i Hi; unfold S1; rewrite code_at_cat; reflexivity | exact TL]. }
    assert (TD1 : tab_ok DISTS (fun i => code_at S1 f_distcode i) f_distbits extD = true).
    { apply (tab_ok_ext DISTS (fun i => cat f_codes f_distcode i)); [intros i Hi; unfold S1; rewrite code_at_cat; reflexivity | exact TD]. }
    assert (XWL : x_wsize XX <> 0 -> arr_len (x_window XX) = x_wsize XX) by (unfold XX; cbn [x_wsize x_window]; intros; lia).
    destruct (loop_spec XX S1 NI NO NO32 ltac:(unfold XX; cbn [x_input]; exact Cinb) ltac:(unfold XX; cbn [x_window]; exact Swinb)
                ltac:(reflexivity) ltac:(unfold XX; cbn [x_sane]; liaq) ltac:(unfold XX; cbn [x_whave x_wsize]; liaq) ltac:(unfold XX; cbn [x_wnext x_wsize]; liaq)
                XWL ltac:(unfold XX; cbn [x_wsize]; liaq) XL XD extL extD TL1 TD1
                ltac:(unfold XX; cbn [x_last]; liaq) ltac:(unfold XX; cbn [x_end]; liaq)
                (Z.to_nat (8 * r_have + r_left + 79)) r_next r_put r_hold r_bits 0 0 0 (FOut 0) c_outbuf
                ltac:(liaq) ltac:(liaq) ltac:(split; [exact ClNO | exact Coutb]) ltac:(liaq) ltac:(liaq) ltac:(liaq) ltac:(liaq))
      as (h1 & H1 & M1 & L1 & G & P).
    rewrite G. split; [reflexivity|].
    specialize (HD h1 H1 M1).
    match type of HD with lcons ?S0 h1 + _ + _ >= _ =>
      replace (lcons S1 h1) with (lcons S0 h1) in P by (symmetry; exact (lcons_hb S0 r_hold r_bits h1));
      replace (lcons S1 h1) with (lcons S0 h1) in L1 by (symmetry; exact (lcons_hb S0 r_hold r_bits h1)) end.
    clear TL1 TD1 XWL XL XD G.
    unfold LPOST in P.
    destruct (iterK_nat _ (fstep_fn XX S1) _) as [a'|[f' mm]]; cbn [lres fst snd] in P.
    1: destruct a' as [fi fo fh fb fl fd fop ffr fob]; destruct P as (Bf & OBf & Of & If & Cf & _).
    2: destruct f' as [fi fo fh fb fl fd fop ffr fob]; destruct P as (Bf & OBf & Of & If & Cf & Mf);
       destruct mm as [[md mmsg]|]; [destruct mmsg as [msg|] |].
    all: unfold FB in Bf; cbn [f_in f_out InflateFast.f_hold InflateFast.f_bits f_ob] in Bf, OBf, Of, If, Cf; fred.
    all: unfold XX; cbn [x_last x_end].
    all: rewrite !avail_if.
    all:
         rewrite (Z.shiftl_mul_pow2 (Z.shiftr fb 3) 3) by liaq; rewrite (Z.shiftr_div_pow2 fb 3) by liaq; change (2 ^ 3) with 8;
         pose proof (Z.div_mod fb 8 ltac:(liaq)) as DM; pose proof (Z.mod_pos_bound fb 8 ltac:(liaq)) as MB;
         set (q := fb / 8) in *;
         rewrite (wrap32_id (fb - q * 8)) by liaq;
         rewrite (zmask_ones (fb - q * 8)) by liaq; rewrite (Z.min_l (fb - q * 8) 32) by liaq;
         pose proof (land_ones_bound fh (fb - q * 8) ltac:(liaq)) as HB';
         repeat match goal with |- context [wrap32 ?e] => rewrite (wrap32_id e) by liaq end;
         destruct OBf as [OBl OBb].
    all: assert (Hq : 0 <= fi - q) by liaq.
    all: assert (P64 : 2 ^ (fb - q * 8) <= 2 ^ 7) by (apply Z.pow_le_mono_r; liaq); change (2 ^ 7) with 128 in P64.
    all: try (destruct Mf as [-> | ->]).
    all: split; [| split; [liaq | phi_auto]].
    all: unfold InflateInv.pinv; cbn [w_s]; split; [exact B|]; split; [| split; [| split; [| split]]].
    1,6,11,16,21,26: apply LRNGq_mk; [srng_close; conj_solve | cinv_close; conj_solve | rinv_close; conj_solve | winv_close; exact WI
                          | cross_close; replace (c_total_out + (r_out - (257 + (r_put + (r_left - 257)) - fo))) with (c_total_out + (r_out - r_left) + (fo - r_put)) by liaq;
                            rewrite <- (Z.add_assoc TOT0 r_put (fo - r_put)) || replace (TOT0 + fo) with (TOT0 + r_put + (fo - r_put)) by liaq;
                            apply wrap64_add_eq; exact CR].
    1,5,9,13,17,21: match type of SIr with sinv ?S0 =>
        first [ exact (sinv_hb S0 _ _ SIr)
              | exact (sinv_plain (iset_bits (iset_hold S0 _) _) BAD (sinv_hb S0 _ _ SIr) plain_BAD)
              | exact (sinv_plain (iset_bits (iset_hold S0 _) _) TYPE (sinv_hb S0 _ _ SIr) plain_TYPE) ] end.
    1,4,7,10,13,16: xinv_close; split; [destruct Xret as [Xr|Xr]; [left; exact Xr | exfalso; clear -Xr Klen Kbad; liaq] |]; split; [liaq|]; left; liaq.
    1,3,5,7,9,11: unfold binv; cbn [w_s w_r ir_bits]; left; liaq.
    all: kinv_close; kinv_auto.
  Qed.
End Call.
