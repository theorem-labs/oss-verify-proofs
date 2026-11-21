(** * Bridge.IBoundary — INTERFACE (part C lead): what each group delivers, and how it composes.

    compress_fuzzer's asserts (CK1 length, CK2 bytes) hold at level [L] once
    three facts are available:

      [BrCompressCall]    deflate groups (D, M): S5's one compress call
                          returns RT's [zr_deflate L 15] bytes;
      [BrUncompressCall]  inflate group (I): S5's one uncompress call returns
                          RT's [zr_inflate Z_NO_FLUSH 15 n] bytes;
      [RtCompressPath L]  the round-trip side: RT's own compress/uncompress
                          round trip at level L (a worker's
                          [zr_l<L>z_compress_path], all levels 0-9).

    [harness_no_ckfail] is the composition: those three give
    [harness_outC d <> HC_exit k] for every input whose level byte selects
    [L].  It is stated here so that the deliverables are pinned before any
    group starts, and proved here.

    Ownership: the part C lead. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZHarnessL ZApiC ZHarnessC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZIface ZApiInst ZApiInstC Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZRepro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Chunk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition byte_list (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.

(** The deflate side's deliverable.  [zdc_deflate] is the call the harness's
    compress2 loop makes first (the whole input, [avail_out = compressBound],
    [Z_FINISH] = 4); when RT's one-call deflate succeeds, S5's returns the
    same bytes and [Z_STREAM_END] (= 1), reports a consumed count within the
    input, and counts its output in [total_out].  (The count was [= length
    data] until 2026-10-20: the loop ends on [Z_STREAM_END] whatever the count,
    and neither model states "end of stream reads all input" in general;
    a worker.) *)
Definition BrCompressCall : Prop :=
  forall level data enc,
    0 <= level <= 9 -> byte_list data -> ZIface.zlength data <= 1048573 ->
    ZRepro.zr_deflate level 15 data = Some enc ->
    let '(ds', consumed, out, rc) :=
      ZApiInstC.zdc_deflate data (ZApiInstC.zdc_init level)
                            (Z.Deflate.compressBound_m (ZIface.zlength data)) 4 in
    out = enc /\ rc = 1 /\ 0 <= consumed <= ZIface.zlength data
    /\ ZIface.zs_total_out (ZApiInst.dz_z ds') = ZIface.zlength out
    /\ byte_list out.

(** The inflate side's deliverable: the harness's first uncompress call
    (whole input, [avail_out = n], window allocation granted).  The input
    fits a [uInt]: S5 keeps [avail_in] mod 2^32 and RT does not, so for a
    longer [enc] (a stream followed by junk) the two differ; compress's output is far below the bound. *)
Definition BrUncompressCall : Prop :=
  forall n enc x,
    0 < n <= 1048573 -> byte_list enc -> ZIface.zlength enc <= ZC_UMAX ->
    ZRepro.zr_inflate 0 15 n enc = Some x ->
    let '(is', _, out, rc) := ZApiInstC.zic_inflate enc ZApiInst.zi_init n true in
    out = x /\ rc = 1 /\ ZIface.zs_total_out (ZApiInst.iz_z is') = ZIface.zlength out.

(** The round-trip side's deliverable at level [L]: verbatim the statement of
    [zr_l<L>z_compress_path] in [roundtrip/model/RtL<L>ZRt.v] (a worker,
    commit , all ten levels, Closed under the global context), so
    each of those theorems proves [RtCompressPath L] by [exact] once the two
    trees share a build. *)
Definition RtCompressPath (L : Z) : Prop :=
  forall x, ZRepro.ZR_Input x ->
    exists enc, ZRepro.zr_deflate L 15 x = Some enc
             /\ Chunk.zlen enc <= Chunk.zlen x + Z.shiftr (Chunk.zlen x) 12 + Z.shiftr (Chunk.zlen x) 14
                                  + Z.shiftr (Chunk.zlen x) 25 + 13
             /\ ZRepro.zr_inflate 0 15 (Chunk.zlen x) enc = Some x.

(* ------------------------------------------------------------------------- *)
(* The composition                                                           *)
(* ------------------------------------------------------------------------- *)

Lemma iterZL_first : forall {A B} n (step : A -> A + B) dflt a b,
  0 < n -> step a = inr b -> iterZL n step dflt a = b.
Proof.
  intros A B n step dflt a b Hn Hs. rewrite iterZL_nat.
  replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia. cbn [iterNL]. rewrite Hs. reflexivity.
Qed.

Lemma rev_append_twice : forall (l : list Z), rev_append (rev_append l []) [] = l.
Proof. intros l. rewrite !rev_append_rev, !app_nil_r. apply rev_involutive. Qed.

Lemma ztake_all : forall (l : list Z), ztake (zlength l) l = l.
Proof. intros l. unfold ztake, zlength. rewrite Nat2Z.id. apply firstn_all. Qed.

Lemma bufC_self : forall (l : list Z), bufC l (zlength l) = l.
Proof.
  intros l. unfold bufC, zrepeat. rewrite Z.sub_diag. cbn [Z.to_nat repeat]. rewrite app_nil_r.
  unfold zlength. rewrite Nat2Z.id. apply firstn_all.
Qed.

Lemma Forall_skipn_Z : forall (P : Z -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof.
  induction n as [|n IH]; intros l H; [exact H|]. destruct l as [|x l]; [constructor|].
  inversion H as [|? ? _ Hl]; subst. apply IH, Hl.
Qed.

(** compressBound at the harness's sizes: no 64-bit wrap, and well inside a [uInt]. *)
Lemma cb_value : forall n, 0 <= n <= 1048576 ->
  Z.Deflate.compressBound_m n = n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13
  /\ n + 13 <= n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13 <= 2 * n + 13.
Proof.
  intros n Hn. rewrite !Z.shiftr_div_pow2 by lia.
  assert (A : forall k, 2 <= k -> 0 <= n / 2 ^ k <= n / 4).
  { intros k Hk. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
    apply Z.div_le_compat_l; [lia|]. split; [lia|].
    replace 4 with (2 ^ 2) by reflexivity. apply Z.pow_le_mono_r; lia. }
  pose proof (A 12 ltac:(lia)). pose proof (A 14 ltac:(lia)). pose proof (A 25 ltac:(lia)).
  pose proof (Z.mul_div_le n 4 ltac:(lia)).
  split; [|lia].
  unfold Z.Deflate.compressBound_m, Z.Deflate.sat_bound64. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite ZIface.wrap64_id by (change (2 ^ 64) with 18446744073709551616; lia).
  (* zlib 1.4 (zl14cmp-r1): compressBound saturates; on this range the sum is at least n, so it does not *)
  match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b) end; [lia | reflexivity].
Qed.

Lemma total0 : forall L, 0 <= L <= 9 -> ZIface.zs_total_out (ZApiInst.dz_z (ZApiInstC.zdc_init L)) = 0.
Proof.
  intros L HL.
  assert (H : L = 0 \/ L = 1 \/ L = 2 \/ L = 3 \/ L = 4 \/ L = 5 \/ L = 6 \/ L = 7 \/ L = 8 \/ L = 9) by lia.
  repeat (destruct H as [->|H]; [vm_compute; reflexivity|]). subst. vm_compute. reflexivity.
Qed.

(** The harness's compress2 loop, when its first call ends the stream (pair D6): the loop
    stops on [Z_STREAM_END] whatever the call reports as consumed. *)
Lemma c2_first : forall L data enc ds' consumed,
  0 <= L <= 9 -> zlength data <= 1048573 -> 0 <= consumed <= zlength data ->
  ZApiInstC.zdc_deflate data (ZApiInstC.zdc_init L) (Z.Deflate.compressBound_m (zlength data)) 4
    = (ds', consumed, enc, 1) ->
  ZIface.zs_total_out (ZApiInst.dz_z ds') = zlength enc ->
  zlength enc <= Z.Deflate.compressBound_m (zlength data) ->
  c2_pure ZApiInstC.zinstC (Z.Deflate.compressBound_m (zlength data)) data L = Some (enc, zlength enc, Z_OK).
Proof.
  intros L data enc ds' consumed HL Hn Hc Hd Ht Hb.
  assert (Hn0 : 0 <= zlength data) by (unfold zlength; lia).
  destruct (cb_value (zlength data) ltac:(lia)) as [HNv HNb]; rewrite <- HNv in HNb.
  set (N := Z.Deflate.compressBound_m (zlength data)) in *.
  assert (HNU : (ZC_UMAX <? N) = false) by (apply Z.ltb_ge; unfold ZC_UMAX; lia).
  assert (HdU : (ZC_UMAX <? zlength data) = false) by (apply Z.ltb_ge; unfold ZC_UMAX; lia).
  assert (Hok : c_step_ok ZApiInstC.zinstC (zlength data) N (ZApiInstC.zdc_init L) ds' consumed enc = true).
  { unfold c_step_ok.
    change (dc_total_out ZApiInstC.zinstC ds') with (ZIface.zs_total_out (ZApiInst.dz_z ds')).
    change (dc_total_out ZApiInstC.zinstC (ZApiInstC.zdc_init L))
      with (ZIface.zs_total_out (ZApiInst.dz_z (ZApiInstC.zdc_init L))).
    rewrite Ht, (total0 L HL).
    assert (Hel : 0 <= zlength enc) by (unfold zlength; lia).
    repeat rewrite andb_true_iff. rewrite !Z.leb_le, Z.eqb_eq. lia. }
  assert (Hstep : exists x', c2_stepP ZApiInstC.zinstC (c2_x0 ZApiInstC.zinstC N data L) = inr (Some (x', 1))
                            /\ c2_ds ZApiInstC.zinstC x' = ds' /\ c2_orev ZApiInstC.zinstC x' = rev_append enc []).
  { unfold c2_stepP, c2_refill, c2_x0.
    cbn [c2_aout c2_ain c2_left c2_slen c2_rest c2_ds c2_orev Z.eqb].
    rewrite HNU, HdU. cbn iota beta zeta. rewrite !Z.sub_diag.
    cbn [c2_flush Z.eqb]. unfold Z_FINISH.
    change (dc_deflate ZApiInstC.zinstC) with ZApiInstC.zdc_deflate.
    change (dc_init ZApiInstC.zinstC L) with (ZApiInstC.zdc_init L).
    rewrite ztake_all, Hd. cbn iota beta zeta. rewrite Hok. cbn [Z.eqb Z_OK].
    eexists. split; [reflexivity|]. split; reflexivity. }
  destruct Hstep as (x' & Hs & Hds & Hor).
  unfold c2_pure, c2_loop.
  rewrite (iterZL_first (C2_FUEL N (zlength data)) _ _ _ _ ltac:(unfold C2_FUEL; lia) Hs).
  cbv zeta. rewrite Hor, Hds, rev_append_twice.
  change (dc_total_out ZApiInstC.zinstC ds') with (ZIface.zs_total_out (ZApiInst.dz_z ds')).
  rewrite Ht, Z.eqb_refl. replace (zlength enc <=? N) with true by (symmetry; apply Z.leb_le; exact Hb).
  reflexivity.
Qed.

(** The harness's uncompress loop, when its first call ends the stream. *)
Lemma u2_first : forall n enc x is' consumed,
  0 < n <= 1048576 -> zlength enc <= ZC_UMAX ->
  ZApiInstC.zic_inflate enc ZApiInst.zi_init n true = (is', consumed, x, 1) ->
  zlength x = n -> ZIface.zs_total_out (ZApiInst.iz_z is') = zlength x ->
  u2_pure ZApiInstC.zinstC n enc = Some (x, n, Z_OK).
Proof.
  intros n enc x is' consumed Hn Hel Hi Hx Ht.
  assert (HnU : (ZC_UMAX <? n) = false) by (apply Z.ltb_ge; unfold ZC_UMAX; lia).
  assert (HeU : (ZC_UMAX <? zlength enc) = false) by (apply Z.ltb_ge; lia).
  assert (Hok : u_step_ok (zlength enc) n consumed x 1 = true).
  { unfold u_step_ok. rewrite Hx, Z.leb_refl. reflexivity. }
  assert (Hstep : exists x', u2_stepP ZApiInstC.zinstC true (u2_x0 ZApiInstC.zinstC n enc) = inr (Some (x', 1))
                            /\ u2_is ZApiInstC.zinstC x' = is' /\ u2_orev ZApiInstC.zinstC x' = rev_append x []
                            /\ u2_left ZApiInstC.zinstC x' = n - n /\ u2_aout ZApiInstC.zinstC x' = n - zlength x).
  { unfold u2_stepP, u2_refill, u2_x0.
    cbn [u2_aout u2_ain u2_left u2_len u2_rest u2_is u2_orev Z.eqb].
    rewrite HnU, HeU. cbn iota beta zeta.
    change (ic_inflate ZApiInstC.zinstC) with ZApiInstC.zic_inflate.
    change (ic_init ZApiInstC.zinstC) with ZApiInst.zi_init.
    rewrite ztake_all, Hi. cbn iota beta zeta. rewrite Hok. cbn [Z.eqb Z_OK].
    eexists. split; [reflexivity|]. repeat split; reflexivity. }
  destruct Hstep as (x' & Hs & His & Hor & HL & HA).
  unfold u2_pure, u2_loop.
  rewrite (iterZL_first (U2_FUEL n (zlength enc)) _ _ _ _ ltac:(unfold U2_FUEL, zlength in *; lia) Hs).
  (* zlib 1.4: the length is n - (left + avail_out), here n - (0 + (n - |x|)) = |x| = n *)
  unfold u2_result, u2_rc. rewrite Hor, rev_append_twice, HL, HA, Hx.
  replace (n - (n - n + (n - n))) with n by lia. reflexivity.
Qed.

Theorem harness_no_ckfail : forall L,
  0 <= L <= 9 -> BrCompressCall -> BrUncompressCall -> RtCompressPath L ->
  forall d k, sel_level (norm8 d) = L -> harness_outC ZApiInstC.zinstC d <> HC_exit k.
Proof.
  intros L HL HC HU HR d k Hsel. unfold harness_outC. cbv zeta.
  destruct ((zlength d <? ZC_MIN) || (ZC_MAX <? zlength d)) eqn:Hsz; [discriminate|].
  apply orb_false_iff in Hsz as [H1 H2]. apply Z.ltb_ge in H1, H2. unfold ZC_MIN, ZC_MAX in H1, H2.
  set (data := zdrop 3 (norm8 d)).
  assert (Hdl : zlength data = zlength d - 3).
  { unfold data, zdrop, zlength, norm8. rewrite length_skipn, length_map. unfold zlength in H1. lia. }
  assert (Hdb : byte_list data) by (apply Forall_skipn_Z, norm8_bytes).
  assert (Hin : ZRepro.ZR_Input data).
  { split; [exact Hdb|]. change (Chunk.zlen data) with (zlength data). unfold ZRepro.ZR_MAX_INPUT. lia. }
  destruct (HR data Hin) as (enc & Hdef & Hbound & Hinf).
  change (Chunk.zlen data) with (zlength data) in Hbound, Hinf.
  change (Chunk.zlen enc) with (zlength enc) in Hbound.
  specialize (HC L data enc HL Hdb ltac:(change (ZIface.zlength data) with (zlength data); lia) Hdef).
  destruct (ZApiInstC.zdc_deflate data (ZApiInstC.zdc_init L)
              (Z.Deflate.compressBound_m (ZIface.zlength data)) 4) as [[[ds' consumed] out] rc] eqn:Ed.
  destruct HC as (-> & -> & Hcons & Htot & Hencb).
  rewrite Hsel. unfold check_level_pure.
  change (zc_bound ZApiInstC.zinstC (zlength d - 3)) with (Z.Deflate.compressBound_m (zlength d - 3)).
  rewrite <- Hdl.
  destruct (cb_value (zlength data) ltac:(lia)) as [HNv HNb]; rewrite <- HNv in HNb.
  rewrite (c2_first L data enc ds' consumed HL ltac:(lia) Hcons Ed Htot ltac:(rewrite HNv; exact Hbound)).
  rewrite (norm8_id enc Hencb).
  specialize (HU (zlength data) enc data ltac:(lia) Hencb
                ltac:(change (ZIface.zlength enc) with (zlength enc); unfold ZC_UMAX; lia) Hinf).
  destruct (ZApiInstC.zic_inflate enc ZApiInst.zi_init (zlength data) true) as [[[is' c'] out'] rc'] eqn:Ei.
  destruct HU as (-> & -> & Htot').
  rewrite (u2_first (zlength data) enc data is' c' ltac:(lia)
             ltac:(unfold ZC_UMAX; lia) Ei eq_refl Htot').
  rewrite Z.eqb_refl, bufC_self, (norm8_id data Hdb).
  replace (zlist_eqb data data) with true by (symmetry; apply zlist_eqb_eq; reflexivity).
  cbn [negb]. destruct (check_decompress_pure _ _ _ _ _); discriminate.
Qed.
