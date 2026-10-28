(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import FmtFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import FmtFp_split.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import FmtFp_facts_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition run_to_dn (yv fl p t : Z) (p1 r0 : Z) (big : list Z) (a z : Z) : Prop :=
  exists y1 fr e0 y e2 b' z' y' s e2',
    fst (fst (ffp_sign yv fl)) = y1 /\
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) /\
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) /\
    p1 = (if p <? 0 then 6 else p) /\ r0 = (if e2 <? 0 then 0 else 122) /\
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, r0, y) = Some (b', z', y') /\
    fmt_fp_up UP_FUEL (b', r0, z', e2) = Some s /\
    fmt_fp_dn DN_FUEL p1 t r0 s = Some (big, a, z, e2').

Definition words_all_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall i, 0 <= znth big i < 1000000000.

Definition carry_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall e prefix pl bigR aR zR eR,
    ffp_e big a r0 z = Some e ->
    ffp_R t p1 prefix pl big a r0 z e (ffp_j t p1 e) = Some (bigR, aR, zR, eR) ->
    0 <= aR.

Definition azr_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall e prefix pl bigR aR zR eR zS,
    ffp_e big a r0 z = Some e ->
    ffp_R t p1 prefix pl big a r0 z e (ffp_j t p1 e) = Some (bigR, aR, zR, eR) ->
    fmt_fp_strip BIG_FUEL bigR aR zR = Some zS ->
    Z.lor t 32 <> CHR_f -> zS <= aR -> aR = r0.

Definition yn_fact (y : Z) : Prop :=
  Z.land (Z.shiftr (hi64 y) 48) 0x7fff <> 0 \/ f128_le y F128_ZERO = 0.

Definition below_a_fact (yv fl p t : Z) : Prop :=
  forall p1 r0 big a z, run_to_dn yv fl p t p1 r0 big a z ->
  forall k, 0 <= k < a -> znth big k = 0.
