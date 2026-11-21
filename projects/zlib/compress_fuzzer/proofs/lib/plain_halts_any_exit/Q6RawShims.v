(** * Q6RawShims — the three wrap-0 (raw) arm shims for the inflater walk.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20; TL
    assignment: ZRepro_Inflater_raw).  At windowBits -15 the header sets
    [h_wrap = 0] ([zr_iwrap_probe] pins (0,15)), and the three
    wrap-sensitive arms each take their raw branch DEFINITIONALLY:

    - HEAD: no header bytes — one composite step into TYPEDO, so the
      walk's correspondence is established at bit-position 0 with an
      empty accumulator (the raw replacement for ZReproQ6B's wrap-5
      two-byte read).
    - CHECK: no 32-bit trailer read, no check compare — straight to
      LENGTH.
    - LENGTH: the [wrap <> 0 && flags <> 0] guard is false — straight to
      DONE.

    Stated as named rewrite equations so any walk shape (model-rt's
    stage-3 iteration lemma, or a raw-specific assembly) consumes them
    by [rewrite] without touching the wrap-5 legs.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Inflate.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** HEAD at wrap 0: [inflate.c:589-592]. *)
Lemma zr_raw_head : forall c q,
  h_wrap (s_hdr (q_st q)) = 0 ->
  inf_HEAD c q = inf_TYPEDO c (qmode q M_TYPEDO).
Proof.
  intros c q HW. unfold inf_HEAD. rewrite HW. reflexivity.
Qed.

(** CHECK at wrap 0: the [:1188] wrap test. *)
Lemma zr_raw_check : forall q,
  h_wrap (s_hdr (q_st q)) = 0 ->
  inf_CHECK q = inf_LENGTH (qmode q M_LENGTH).
Proof.
  intros q HW. unfold inf_CHECK. rewrite HW. reflexivity.
Qed.

(** LENGTH at wrap 0: the [:1209] guard is false. *)
Lemma zr_raw_length : forall q,
  h_wrap (s_hdr (q_st q)) = 0 ->
  inf_LENGTH q = inf_DONE (qmode q M_DONE).
Proof.
  intros q HW. unfold inf_LENGTH. rewrite HW. reflexivity.
Qed.

Print Assumptions zr_raw_head.
Print Assumptions zr_raw_check.
Print Assumptions zr_raw_length.
