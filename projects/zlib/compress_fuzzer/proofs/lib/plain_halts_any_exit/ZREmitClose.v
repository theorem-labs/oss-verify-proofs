(** * ZREmitClose — the emitter faces, closed (zero-premise names).

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).

    a5-assembler's face-closure convention (ledger md5 ): the
    assembly consumes ZRepro_Emitter_*_holds with NO premises — the seam
    hypotheses their owners discharged are applied HERE, once.
    Bound+Span (both configs) are g6-bound's (ZReproG6Q, from the
    q5-evsnap packs); StaleSeam is this file's, from the packs'
    [EvSnapOk] records via the canon-weakened [ZR_BlfAll]. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZRepro ZRTreeState ZREvSnap SwEv ZRThread ZREmitBody ZREmitFace ZRGzFace
  ZReproG6Q Gap7Strict.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Theorem zr_staleseam_holds : ZR_StaleSeam.
Proof.
  intros x g sd bs s' evs Hx P.
  destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEvs & _).
  eapply Forall_impl; [|exact HEvs].
  intros ev HE.
  destruct HE as ((_ & Hblf & _) & _).
  unfold ZR_BlfAll.
  intros i Hi.
  apply Hblf. unfold BL_CODES. exact Hi.
Qed.

Theorem zr_gzstaleseam_holds : ZR_GzStaleSeam.
Proof.
  intros x g sd bs s' evs Hx P.
  destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEvs & _).
  eapply Forall_impl; [|exact HEvs].
  intros ev HE.
  destruct HE as ((_ & Hblf & _) & _).
  unfold ZR_BlfAll.
  intros i Hi.
  apply Hblf. unfold BL_CODES. exact Hi.
Qed.

Theorem ZRepro_Emitter_default_zlib_holds : ZRepro_Emitter_default_zlib.
Proof.
  exact (emitter_face_modulo3 zr_boundseam_holds zr_spanseam_holds
           zr_staleseam_holds).
Qed.

Theorem ZRepro_Emitter_l9_gzip_holds : ZRepro_Emitter_l9_gzip.
Proof.
  exact (emitter_face_gz_modulo3 zr_gzboundseam_holds zr_gzspanseam_holds
           zr_gzstaleseam_holds).
Qed.

Print Assumptions ZRepro_Emitter_default_zlib_holds.
Print Assumptions ZRepro_Emitter_l9_gzip_holds.

(** q7 F4: the body slices decode to within one byte — the Z_FINISH
    windup pad is the only leftover.  Same seams, zero premises. *)
Theorem ZR_BodyValidZlib_holds : ZR_BodyValidZlib.
Proof.
  exact (bodyvalid_modulo3 zr_boundseam_holds zr_spanseam_holds
           zr_staleseam_holds).
Qed.

Theorem ZR_BodyValidGzip_holds : ZR_BodyValidGzip.
Proof.
  exact (gz_bodyvalid_modulo3 zr_gzboundseam_holds zr_gzspanseam_holds
           zr_gzstaleseam_holds).
Qed.

Print Assumptions ZR_BodyValidZlib_holds.
Print Assumptions ZR_BodyValidGzip_holds.

(** GAP7 strict decode: MACHINE-accept success on the emitted bodies,
    modulo the two frozen statements (g1's characterization bridge and
    the ENOUGH residue) — the seams are the landed zero-premise ones. *)
Theorem ZR_BodyStrictZlib_of :
  build_accepts_of_kraft_STMT -> EnoughFits_STMT -> ZR_BodyStrictZlib.
Proof.
  intros HBK EFR.
  exact (bodystrict_modulo3 HBK EFR zr_boundseam_holds zr_spanseam_holds
           zr_staleseam_holds).
Qed.

Theorem ZR_BodyStrictGzip_of :
  build_accepts_of_kraft_STMT -> EnoughFits_STMT -> ZR_BodyStrictGzip.
Proof.
  intros HBK EFR.
  exact (gz_bodystrict_modulo3 HBK EFR zr_gzboundseam_holds
           zr_gzspanseam_holds zr_gzstaleseam_holds).
Qed.

Print Assumptions ZR_BodyStrictZlib_of.
Print Assumptions ZR_BodyStrictGzip_of.
