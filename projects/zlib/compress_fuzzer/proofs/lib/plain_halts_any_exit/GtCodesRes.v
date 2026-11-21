(** * GtCodesRes — THE BRIDGE CLOSURE: ZrCodesFetchRes HOLDS.

    [zr_codes_fetch_res_from_own] (GtCodesBridge, q7-decode) applied to
    [zr_codes_own_holds] (KeyCodes, an earlier development run keystone assembly). The
    two [zr_codes_own] Definitions are byte-identical duplicates
    (KeyCodes header declares the duplication), so the application
    crosses by conversion.

    LANDING NOTE (home ruling): GtCodesBridge is [zr_codes_own]'s home;
    KeyCodes re-points at landing (q4's edit — see the joint manifest's
    re-point list). This file then reads entirely at landed names. *)

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6TblChain
  GtCodesBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import KeyCodes.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Theorem zr_codes_fetch_res_holds : ZrCodesFetchRes.
Proof.
  exact (GtCodesBridge.zr_codes_fetch_res_from_own
           KeyCodes.zr_codes_own_holds).
Qed.

Print Assumptions zr_codes_fetch_res_holds.
