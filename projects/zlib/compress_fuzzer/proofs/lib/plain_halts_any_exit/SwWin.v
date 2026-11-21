(** * SwWin — the slow-path walk, part W1a: the window/input correspondence
      invariant, [read_buf]'s contract, and the checksum thread.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W1 of the Q5
    plan (PLAN.md §3-4).  Home is the top
    level, not Spec/PngModel, because this file consumes the GtAdlerChunk /
    GtCrcChunk kits (top-level) — the same layering GtItTotal/GtUsedBits use.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    THE INVARIANT.  [zs_done] is [read_buf]'s ghost trace of consumed input
    (in order, already [u8]-normalised).  [WinInv g slid l st] says the
    window's VALID REGION [0 .. strstart+lookahead) is the last
    [strstart+lookahead] consumed bytes — i.e. window index [i] holds input
    byte [slid + i], where [slid] is the total amount the window has slid.
    Everything the emitter ever reads out of the window (match bytes, the
    stored arm's [win_take], the tally's literals) becomes a fact about the
    INPUT through this record.

    [CkInv] is the checksum thread: [zs_adler] equals the closed form over
    [zs_done], per wrap family, so the trailer clause of the frame falls out
    at the end of the walk instead of needing its own induction.  The
    composition steps are GtAdlerChunk's [adler32_z_chunk] (AdWf-guarded —
    that guard is load-bearing, see that file's §5) and GtCrcChunk's
    alignment-agnostic [crc32_z_at_chunk].

    WRAP-GENERICITY.  Everything here takes [wrap] as a parameter; only
    [CkInv]'s arms distinguish 1 (zlib/adler) from 2 (gzip/crc).  The
    level-9 gzip consumer reads the same lemmas. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Deflate StoredRt.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtAdlerChunk GtCrcChunk.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. The records *)

(** The geometry facts the walk needs.  All four z-repro configs satisfy
    them ([swwin_geom_zr] below, by computation through [defl_init2]). *)
Record GeomOk (g : DeflGeom) : Prop := mkGeomOk {
  (* 512, not 262: [deflateInit2_] forces [windowBits = 8] up to 9
     ("until the window handling is fixed"), so every real geometry has
     [w_size >= 512]; the slack past 262 is what keeps a post-slide
     [strstart] strictly positive ([sp_sslb]'s right disjunct). *)
  go_ws_lo  : 512 <= dg_w_size g;
  go_ws_hi  : 2 * dg_w_size g < 4294967296;
  go_maxd   : dg_max_dist g = dg_w_size g - 262
}.

Record WinInv (g : DeflGeom) (slid : Z) (l : LSt) (st : ZStrm) : Prop
  := mkWinInv {
  wi_ss     : 0 <= ls_strstart l;
  wi_la     : 0 <= ls_lookahead l;
  wi_room   : ls_strstart l + ls_lookahead l <= ls_windowsize l;
  wi_wsize  : ls_windowsize l = 2 * dg_w_size g;
  wi_slid   : 0 <= slid;
  wi_done   : zlen (zs_done st) = slid + ls_strstart l + ls_lookahead l;
  wi_totin  : zs_totalin st = zlen (zs_done st);
  wi_bytes  : Forall (fun b => 0 <= b < 256) (zs_done st);
  wi_inbytes: Forall (fun b => 0 <= b < 256) (zs_in st);
  wi_win    : forall i, 0 <= i < ls_strstart l + ls_lookahead l ->
              ls_window l i = nth (Z.to_nat (slid + i)) (zs_done st) 0
}.

(** The checksum thread, per wrap family.  The initial accumulators are the
    tree's own expressions ([deflate_reset]), not literals. *)
Definition CkInv (wrap : Z) (st : ZStrm) : Prop :=
  (wrap = 1 ->
     zs_adler st = adler32_z (adler32_z 0 true []) false (zs_done st))
  /\ (wrap = 2 ->
     zs_adler st = crc32_z_at (crc32_z 0 true 0 []) 0 (zs_done st)).

(** What one state-to-state move of the fill machinery preserves: the
    invariant itself, the INPUT-INDEX conservation of every position field a
    slide adjusts, the fields it never touches, and the stream's untouched
    output side.  [StepPres] composes ([steppres_trans]); the fill lemmas in
    SwFill.v conclude it. *)
Record StepPres (g : DeflGeom) (slid slid' : Z) (l l' : LSt)
                (st st' : ZStrm) : Prop := mkStepPres {
  sp_inv    : WinInv g slid' l' st';
  sp_grow   : slid <= slid';
  sp_ss     : slid' + ls_strstart l' = slid + ls_strstart l;
  (* the slide either did not move strstart or left it above MAX_DIST —
     what keeps window-coordinate lower bounds (e.g. the pending literal's
     [strstart >= 1]) alive across a fill *)
  sp_sslb   : ls_strstart l' = ls_strstart l
              \/ dg_max_dist g <= ls_strstart l';
  sp_bs     : slid' + ls_blockstart l' = slid + ls_blockstart l;
  sp_ms     : slid' + ls_matchstart l' = slid + ls_matchstart l;
  sp_lagrow : ls_lookahead l <= ls_lookahead l';
  sp_ml     : ls_matchlen l' = ls_matchlen l;
  sp_pl     : ls_prevlen l' = ls_prevlen l;
  sp_pm     : ls_prevmatch l' = ls_prevmatch l;
  sp_ma     : ls_matchavail l' = ls_matchavail l;
  sp_donex  : exists nd, zs_done st' = zs_done st ++ nd;
  sp_cons   : zs_done st' ++ zs_in st' = zs_done st ++ zs_in st;
  sp_out    : zs_out st' = zs_out st;
  sp_avout  : zs_availout st' = zs_availout st;
  sp_totout : zs_totalout st' = zs_totalout st;
  sp_dtype  : zs_datatype st' = zs_datatype st
}.

Lemma steppres_refl : forall g slid l st,
  WinInv g slid l st -> StepPres g slid slid l l st st.
Proof.
  intros g slid l st Hinv.
  constructor; try reflexivity; try lia; try (left; reflexivity);
    [exact Hinv|].
  exists []. now rewrite app_nil_r.
Qed.

Lemma steppres_trans : forall g slid slid1 slid2 l l1 l2 st st1 st2,
  StepPres g slid slid1 l l1 st st1 ->
  StepPres g slid1 slid2 l1 l2 st1 st2 ->
  StepPres g slid slid2 l l2 st st2.
Proof.
  intros g slid slid1 slid2 l l1 l2 st st1 st2 A B.
  destruct A, B.
  constructor; try assumption; try lia; try congruence.
  (* two goals can remain, in either order: the slide disjunct and the
     done-extension; both closers are self-selecting *)
  all: try (destruct sp_sslb1 as [E2|E2];
            [ rewrite E2; exact sp_sslb0 | right; exact E2 ]).
  all: destruct sp_donex0 as [n1 E1]; destruct sp_donex1 as [n2 E2];
       exists (n1 ++ n2); rewrite E2, E1; now rewrite app_assoc.
Qed.

(** ** 2. [read_buf]'s contract *)

Lemma if_ltb_min : forall a b, (if Z.ltb a b then a else b) = Z.min a b.
Proof.
  intros a b. destruct (Z.ltb_spec a b); [rewrite Z.min_l | rewrite Z.min_r];
    lia.
Qed.

Lemma forall_firstn : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (firstn n l).
Proof.
  intros P n l H. revert n. induction H as [|x l Hx Hl IH]; intros n.
  - now rewrite firstn_nil.
  - destruct n as [|n]; cbn [firstn]; constructor; [exact Hx | apply IH].
Qed.

Lemma forall_skipn : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (skipn n l).
Proof.
  intros P n l H. revert n. induction H as [|x l Hx Hl IH]; intros n.
  - now rewrite skipn_nil.
  - destruct n as [|n]; cbn [skipn]; [now constructor | apply IH].
Qed.

Lemma read_buf_spec : forall wrap size st,
  0 <= size ->
  fst (read_buf wrap size st)
    = map u8 (firstn (Z.to_nat (Z.min size (zlen (zs_in st)))) (zs_in st))
  /\ zs_in (snd (read_buf wrap size st))
       = skipn (Z.to_nat (Z.min size (zlen (zs_in st)))) (zs_in st)
  /\ zs_done (snd (read_buf wrap size st))
       = zs_done st ++ fst (read_buf wrap size st)
  /\ zs_totalin (snd (read_buf wrap size st))
       = zs_totalin st + zlen (fst (read_buf wrap size st))
  /\ zs_out (snd (read_buf wrap size st)) = zs_out st
  /\ zs_availout (snd (read_buf wrap size st)) = zs_availout st
  /\ zs_totalout (snd (read_buf wrap size st)) = zs_totalout st
  /\ zs_datatype (snd (read_buf wrap size st)) = zs_datatype st.
Proof.
  intros wrap size st Hsz.
  unfold read_buf. cbv zeta.
  rewrite if_ltb_min.
  destruct (Z.eqb_spec (Z.min size (zlen (zs_in st))) 0) as [En|En].
  - rewrite En. cbn [fst snd].
    change (Z.to_nat 0) with 0%nat.
    rewrite firstn_O, skipn_O. cbn [map].
    rewrite app_nil_r.
    repeat split; try reflexivity.
    unfold zlen. cbn [length]. lia.
  - cbn [fst snd zs_in zs_done zs_out zs_availout zs_totalin zs_totalout
         zs_datatype setZ_in setZ_done setZ_adler setZ_totalin].
    assert (Hlen : zlen (map u8 (firstn (Z.to_nat (Z.min size (zlen (zs_in st))))
                                   (zs_in st)))
                   = Z.min size (zlen (zs_in st))).
    { unfold zlen. rewrite length_map, length_firstn.
      unfold zlen in *. lia. }
    repeat split; try reflexivity. lia.
Qed.

(** The length of what one call consumes. *)
Lemma read_buf_len : forall wrap size st,
  0 <= size ->
  zlen (fst (read_buf wrap size st)) = Z.min size (zlen (zs_in st)).
Proof.
  intros wrap size st Hsz.
  destruct (read_buf_spec wrap size st Hsz) as [Hdat _].
  rewrite Hdat. unfold zlen. rewrite length_map, length_firstn.
  unfold zlen in *. lia.
Qed.

(** The checksum accumulator after one call, per wrap — spelled on the
    NONEMPTY branch only, because the empty branch returns [st] itself. *)
Lemma read_buf_adler_step : forall wrap size st,
  0 < Z.min size (zlen (zs_in st)) ->
  zs_adler (snd (read_buf wrap size st))
  = (if Z.eqb wrap 1
     then adler32_z (zs_adler st) false (fst (read_buf wrap size st))
     else if Z.eqb wrap 2
     then crc32_z_at (zs_adler st) 0 (fst (read_buf wrap size st))
     else zs_adler st).
Proof.
  intros wrap size st Hpos.
  unfold read_buf. cbv zeta.
  rewrite if_ltb_min.
  destruct (Z.eqb_spec (Z.min size (zlen (zs_in st))) 0) as [En|En];
    [lia|].
  cbn [fst snd zs_adler setZ_in setZ_done setZ_adler setZ_totalin].
  reflexivity.
Qed.

Lemma read_buf_adler_id : forall wrap size st,
  0 <= size ->
  Z.min size (zlen (zs_in st)) <= 0 ->
  snd (read_buf wrap size st) = st.
Proof.
  intros wrap size st Hsz Hle.
  unfold read_buf. cbv zeta.
  rewrite if_ltb_min.
  destruct (Z.eqb_spec (Z.min size (zlen (zs_in st))) 0) as [En|En].
  - reflexivity.
  - exfalso. unfold zlen in *. lia.
Qed.

(** [CkInv] survives one [read_buf], for every wrap. *)
Lemma read_buf_ckinv : forall wrap size st,
  0 <= size ->
  Forall (fun b => 0 <= b < 256) (zs_done st) ->
  CkInv wrap st ->
  CkInv wrap (snd (read_buf wrap size st)).
Proof.
  intros wrap size st Hsz Hdb [Ha Hc].
  destruct (Z.leb_spec (Z.min size (zlen (zs_in st))) 0) as [Hle|Hgt].
  { rewrite (read_buf_adler_id wrap size st Hsz Hle). now split. }
  destruct (read_buf_spec wrap size st Hsz)
    as (Hdat & _ & Hdone & _).
  pose proof (read_buf_adler_step wrap size st Hgt) as Hstep.
  split.
  - intros ->. cbn [Z.eqb] in Hstep.
    rewrite Hstep, Hdone, (Ha eq_refl).
    apply adler32_z_chunk.
    + exact (proj1 adval_init).
    + split; [|discriminate].
      intros b Hb. rewrite Forall_forall in Hdb. now apply Hdb.
    + exact (read_buf_chunk_ad_wf 1 size st).
  - intros ->. cbn [Z.eqb] in Hstep.
    rewrite Hstep, Hdone, (Hc eq_refl).
    apply crc32_z_at_chunk.
    + intros b Hb. rewrite Forall_forall in Hdb. now apply Hdb.
    + pose proof (read_buf_chunk_ad_wf 2 size st) as [Hb _].
      exact Hb.
Qed.

(** ...and at the reset state it holds outright, both wrap families. *)
Lemma ckinv_reset : forall g wrap,
  CkInv wrap (d_strm (deflate_reset g wrap)).
Proof.
  intros g wrap. split; intros ->; vm_compute; reflexivity.
Qed.

(** ** 3. Reading the window back as input bytes *)

Lemma nth_skipn_local : forall (l : list Z) m k d,
  nth k (skipn m l) d = nth (m + k) l d.
Proof.
  induction l as [|x l IH]; intros m k d.
  - now rewrite skipn_nil, !nth_overflow by (cbn [length]; lia).
  - destruct m as [|m]; cbn [skipn].
    + reflexivity.
    + cbn [nth]. apply IH.
Qed.

Lemma nth_firstn_local : forall (l : list Z) a k d,
  (k < a)%nat -> nth k (firstn a l) d = nth k l d.
Proof.
  induction l as [|x l IH]; intros a k d Hk.
  - now rewrite firstn_nil.
  - destruct a as [|a]; [lia|]; cbn [firstn].
    destruct k as [|k]; cbn [nth]; [reflexivity|].
    apply IH; lia.
Qed.

(** The window slice an emitter arm reads IS a slice of the consumed input.
    This is the stored arm's [buf] and the resolve tie's byte source. *)
Lemma wininv_take : forall g slid l st base cnt,
  WinInv g slid l st ->
  0 <= base -> 0 <= cnt ->
  base + cnt <= ls_strstart l + ls_lookahead l ->
  win_take (ls_window l) base cnt
  = firstn (Z.to_nat cnt) (skipn (Z.to_nat (slid + base)) (zs_done st)).
Proof.
  intros g slid l st base cnt Hinv Hb Hc Hbc.
  pose proof (wi_done _ _ _ _ Hinv) as Hdone.
  pose proof (wi_slid _ _ _ _ Hinv) as Hslid.
  assert (Hlen : length (firstn (Z.to_nat cnt)
                    (skipn (Z.to_nat (slid + base)) (zs_done st)))
                 = Z.to_nat cnt).
  { rewrite length_firstn, length_skipn.
    unfold zlen in Hdone. lia. }
  apply (nth_ext _ _ 0 0).
  { unfold win_take. rewrite length_map, length_seq. lia. }
  intros k Hk.
  unfold win_take in Hk |- *.
  rewrite length_map, length_seq in Hk.
  set (f := fun j => ls_window l (base + Z.of_nat j)).
  assert (Hlen2 : (k < length (map f (seq 0 (Z.to_nat cnt))))%nat)
    by (rewrite length_map, length_seq; exact Hk).
  rewrite (nth_indep _ _ (f 0%nat) Hlen2).
  rewrite map_nth. rewrite seq_nth by exact Hk.
  cbn [Nat.add]. unfold f.
  rewrite (wi_win _ _ _ _ Hinv (base + Z.of_nat k)) by lia.
  rewrite nth_firstn_local by lia.
  rewrite nth_skipn_local.
  f_equal. lia.
Qed.

(** ** 4. Geometry instances — the four z-repro configs, by computation

    [defl_init2] at (level, windowBits, memLevel 8, strategy 0) for the four
    driver configs; each geometry satisfies [GeomOk].  The gzip config's
    normalised [w_bits] is 15, so all four share one w_size. *)
Example swwin_geom_zr :
  match defl_init2 (-1) 8 15 8 0, defl_init2 1 8 (-15) 8 0,
        defl_init2 9 8 31 8 0, defl_init2 0 8 15 8 0 with
  | Some g1, Some g2, Some g3, Some g4 =>
      GeomOk g1 /\ GeomOk g2 /\ GeomOk g3 /\ GeomOk g4
  | _, _, _, _ => False
  end.
Proof.
  vm_compute.
  repeat split; vm_compute;
    first [reflexivity | intros H; discriminate H].
Qed.

Print Assumptions read_buf_ckinv.
Print Assumptions wininv_take.
