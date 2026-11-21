(** IBoundary's inflate-side
    deliverables at RT's 1.4 flavour.  DRAFT, not frozen (2026-11-07).

     ruling (A): RT's inflate gets a 1.4 flavour; the 1.3.1 texts stay.  S5's 1.4 inflate is related
    to RT's 1.4 flavour step for step (Bridge/Infl), so group I's deliverable is stated with
    [ZRepro14.zr_inflate14] (RT's [inflate_model14]) instead of [ZRepro.zr_inflate]:

      [BrUncompressCall14]  = [IBoundary.BrUncompressCall] with [zr_inflate14] for [zr_inflate];
      [RtCompressPath14 L]  = [IBoundary.RtCompressPath L] with [zr_inflate14] for [zr_inflate];
      [harness_no_ckfail14] = [IBoundary.harness_no_ckfail] from those two, its proof text verbatim.

    The deflate side keeps [IBoundary.BrCompressCall] (RT's [zr_deflate]); if the 1.4 deflate port needs a
    [zr_deflate14], its twin goes in [BrCompressCall] and in [RtCompressPath14]'s first conjunct. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZHarnessL ZApiC ZHarnessC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZIface ZApiInst ZApiInstC Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZRepro ZRepro14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IBoundary.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** The inflate side's deliverable at 1.4: [IBoundary.BrUncompressCall]'s text, RT's call at 1.4. *)
Definition BrUncompressCall14 : Prop :=
  forall n enc x,
    0 < n <= 1048573 -> byte_list enc -> ZIface.zlength enc <= ZC_UMAX ->
    ZRepro14.zr_inflate14 0 15 n enc = Some x ->
    let '(is', _, out, rc) := ZApiInstC.zic_inflate enc ZApiInst.zi_init n true in
    out = x /\ rc = 1 /\ ZIface.zs_total_out (ZApiInst.iz_z is') = ZIface.zlength out.

(** The round-trip side's deliverable at level [L] and 1.4: [IBoundary.RtCompressPath]'s text, RT's inflate
    at 1.4. *)
Definition RtCompressPath14 (L : Z) : Prop :=
  forall x, ZRepro.ZR_Input x ->
    exists enc, ZRepro.zr_deflate L 15 x = Some enc
             /\ Chunk.zlen enc <= Chunk.zlen x + Z.shiftr (Chunk.zlen x) 12 + Z.shiftr (Chunk.zlen x) 14
                                  + Z.shiftr (Chunk.zlen x) 25 + 13
             /\ ZRepro14.zr_inflate14 0 15 (Chunk.zlen x) enc = Some x.

(** [IBoundary.harness_no_ckfail] at 1.4, its proof text verbatim. *)
Theorem harness_no_ckfail14 : forall L,
  0 <= L <= 9 -> BrCompressCall -> BrUncompressCall14 -> RtCompressPath14 L ->
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
