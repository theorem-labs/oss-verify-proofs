(** * FO.NoCkStandIn — the one hypothesis of compress_fuzzer's plain halts, from part C (integration rehearsal)

    This variant replaces the admitted stand-in of [port/overlays/compress_fuzzer-plain/FO/NoCkStandIn.v] in the
    compress_fuzzer-plain-rt tree, which also carries the round-trip model cone ([roundtrip/model]) and part
    C's bridge ([roundtrip/model-equiv/bridge]).  [NoCkFail] is [harness_no_ckfail_all]'s conclusion verbatim.
    Both of its premises are cited: [BrCompressCall] is group D's theorem ([Bridge.DEmit.DTop.br_compress_call])
    and [BrUncompressCall] is group I's ([Bridge.Infl.ITop.br_uncompress_call]).  This file admits nothing.

    zlib 1.4: group I's deliverable is now
    [IBoundary14.BrUncompressCall14] (RT's inflate at 1.4, ITop r2), and the round-trip side is
    [IRtLink14.harness_no_ckfail_all14] over the FROZEN [IBoundary14.harness_no_ckfail14] and the ten
    RtL<L>ZRt14 producers.  [NoCkFail]'s statement is unchanged. *)

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import TargetSafeR.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IBoundary IBoundary14 IRtLink14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DTop.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require ITop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** Part C, deflate side (groups D and M). *)
Lemma br_compress_call : BrCompressCall.
Proof. exact OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit.DTop.br_compress_call. Qed.

(** Part C, inflate side (group I), at 1.4. *)
Lemma br_uncompress_call14 : BrUncompressCall14.
Proof. exact OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl.ITop.br_uncompress_call. Qed.

Lemma no_ckfail : NoCkFail.
Proof. exact (harness_no_ckfail_all14 br_compress_call br_uncompress_call14). Qed.
