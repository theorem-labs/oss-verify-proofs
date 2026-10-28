(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Sf_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Strategy expand [wrap64 lo64 hi64 add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 is_neg64 lt_s64 sra63 zext32 b2z
                           ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K HALF60 DQUIET].

Definition add_M8 (SHi SLo aExp signHi : Z) : Z :=
  let '(SHi, SLo, aExp) :=
      if negb (lt_s64 0 aExp)
      then (let '(SHi, SLo) := denorm_mirror SHi SLo aExp in (SHi, SLo, 0))
      else (SHi, SLo, aExp) in
  round_mirror SHi SLo aExp signHi.

Definition add_M7 (xHi SHi SLo aExp : Z) : Z :=
  let signHi := shl64 (shr64 xHi 63) 63 in
  if negb (lt_s64 aExp 0x7fff) then mk128 (Z.lor signHi INF_HI) 0
  else add_M8 SHi SLo aExp signHi.

Definition add_M6 (xHi subtraction AHi ALo BHi BLo aExp : Z) : Z :=
  match addsub_mirror subtraction AHi ALo BHi BLo aExp with
  | None => mk128 0 0
  | Some (SHi, SLo, aExp) => add_M7 xHi SHi SLo aExp
  end.

Definition addsub_sub (AHi ALo BHi BLo aExp : Z) : option (Z * Z * Z) :=
  if Z.eqb (Z.lor (Z.lxor ALo BLo) (Z.lxor AHi BHi)) 0 then None
  else
    let borrow := b2z (Z.ltb ALo BLo) in
    let SHi := sub64 (sub64 AHi BHi) borrow in
    let SLo := sub64 ALo BLo in
    if Z.eqb (shr64 SHi 51) 0 then
      let clzS := clz128_mirror SHi SLo in
      let shiftS := sub64 clzS 12 in
      let '(SHi, SLo) := shl128_mirror SHi SLo shiftS in
      let aExp := sub64 aExp shiftS in
      Some (SHi, SLo, aExp)
    else Some (SHi, SLo, aExp).
Definition addsub_add (AHi ALo BHi BLo aExp : Z) : option (Z * Z * Z) :=
  let SLo := add64 BLo ALo in
  let carry := b2z (Z.ltb SLo BLo) in
  let SHi := add64 (add64 BHi AHi) carry in
  if is_neg64 (shl64 SHi 11) then
    let st := Z.land BLo 1 in
    let SLo := Z.lor (Z.lor (shr64 SLo 1) st) (shl64 SHi 63) in
    let SHi := shr64 SHi 1 in
    let aExp := add64 aExp 1 in
    Some (SHi, SLo, aExp)
  else Some (SHi, SLo, aExp).
Definition add_M6s (xHi AHi ALo BHi BLo aExp : Z) : Z :=
  match addsub_sub AHi ALo BHi BLo aExp with
  | None => mk128 0 0
  | Some (SHi, SLo, aExp) => add_M7 xHi SHi SLo aExp
  end.
Definition add_M6a (xHi AHi ALo BHi BLo aExp : Z) : Z :=
  match addsub_add AHi ALo BHi BLo aExp with
  | None => mk128 0 0
  | Some (SHi, SLo, aExp) => add_M7 xHi SHi SLo aExp
  end.

Definition add_M4 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp : Z) : Z :=
  let subtraction := shr64 (Z.lxor bHi aHi) 63 in
  let aSigHi3 := Z.lor (shl64 aSigHi 3) (shr64 aSigLo 61) in
  let bSigHi3 := Z.lor (shl64 bSigHi 3) (Z.lor (shr64 bSigLo 61) IMPL3_HI) in
  let bSigLo3 := shl64 bSigLo 3 in
  let AHi := Z.lor aSigHi3 IMPL3_HI in
  let ALo := shl64 aSigLo 3 in
  let '(BHi, BLo) := align_mirror aExp bExp bSigHi3 bSigLo3 in
  add_M6 xHi subtraction AHi ALo BHi BLo aExp.

Definition add_M3b (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp : Z) : Z :=
  let '(bSigHi, bSigLo, bExp) :=
      if Z.eqb bExp 0 then normalize_mirror bSigHi bSigLo else (bSigHi, bSigLo, bExp) in
  add_M4 aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp.

Definition add_M2 (aHi bHi xLo xHi yLo yHi : Z) : Z :=
  let aExp := shr64 (shl64 xHi 1) 49 in
  let bExp := shr64 (shl64 yHi 1) 49 in
  let aSigHi := Z.land xHi MASK48 in
  let aSigLo := xLo in
  let bSigHi := Z.land yHi MASK48 in
  let bSigLo := yLo in
  let '(aSigHi, aSigLo, aExp) :=
      if Z.eqb aExp 0 then normalize_mirror aSigHi aSigLo else (aSigHi, aSigLo, aExp) in
  add_M3b aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp.

Definition add_M1 (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
  let swap := if Z.eqb bAbsHi aAbsHi then Z.ltb aLo bLo else Z.ltb aAbsHi bAbsHi in
  let '(yLo, yHi, xLo, xHi) := if swap then (aLo, aHi, bLo, bHi) else (bLo, bHi, aLo, aHi) in
  add_M2 aHi bHi xLo xHi yLo yHi.

Strategy expand [addsub_sub addsub_add add_M6s add_M6a].

Lemma add_main_split : forall aLo aHi bLo bHi aAbsHi bAbsHi,
  add_main aLo aHi bLo bHi aAbsHi bAbsHi = add_M1 aLo aHi bLo bHi aAbsHi bAbsHi.
Proof. intros. unfold add_M1, add_M2, add_M3b, add_M4, add_M6, add_M7, add_M8. reflexivity. Qed.

Definition add_S3 (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
  if Z.eqb (Z.lor aLo (Z.lxor aAbsHi INF_HI)) 0 then
    let x := Z.lor (Z.lxor bLo aLo) (Z.lxor (Z.lxor bHi aHi) SIGN64) in
    let m := sub64 (b2z (Z.eqb x 0)) 1 in
    let rhi := if negb (Z.eqb x 0) then aHi else QNAN_HI in
    mk128 rhi (Z.land m aLo)
  else if Z.eqb (Z.lor bLo (Z.lxor bAbsHi INF_HI)) 0 then mk128 bHi bLo
  else if Z.eqb (Z.lor aLo aAbsHi) 0 then
    (if negb (Z.eqb (Z.lor bLo bAbsHi) 0) then mk128 bHi bLo
     else mk128 (Z.land bHi aHi) (Z.land bLo aLo))
  else if negb (Z.eqb (Z.lor bLo bAbsHi) 0) then add_M1 aLo aHi bLo bHi aAbsHi bAbsHi
  else mk128 aHi aLo.

Definition add_S2 (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
  let bIsNaN := if Z.eqb bAbsHi INF_HI then negb (Z.eqb bLo 0) else negb (Z.ltb bAbsHi INF_HI) in
  if bIsNaN then mk128 (Z.lor bHi QUIET_HI) bLo
  else add_S3 aLo aHi bLo bHi aAbsHi bAbsHi.

Definition add_S (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
  let aIsNaN := if Z.eqb aAbsHi INF_HI then negb (Z.eqb aLo 0) else negb (Z.ltb aAbsHi INF_HI) in
  if aIsNaN then mk128 (Z.lor aHi QUIET_HI) aLo
  else add_S2 aLo aHi bLo bHi aAbsHi bAbsHi.

Definition add_top2 (aLo aHi bLo bHi aAbsHi bAbsHi : Z) : Z :=
  let tb := add64 bAbsHi SPEC_K in
  let bSpecial := if Z.eqb tb SPEC_K then Z.eqb bLo 0 else negb (Z.ltb SPEC_K tb) in
  if bSpecial then add_S aLo aHi bLo bHi aAbsHi bAbsHi
  else add_M1 aLo aHi bLo bHi aAbsHi bAbsHi.

Definition add_top (aLo aHi bLo bHi : Z) : Z :=
  let aAbsHi := Z.land aHi ABS_HI in
  let bAbsHi := Z.land bHi ABS_HI in
  let aSpecial := if Z.eqb aAbsHi 0 then Z.eqb aLo 0 else Z.ltb (add64 aAbsHi SPEC_K) SPEC_K in
  let tb := add64 bAbsHi SPEC_K in
  let bSpecial := if Z.eqb tb SPEC_K then Z.eqb bLo 0 else negb (Z.ltb SPEC_K tb) in
  if aSpecial || bSpecial then add_S aLo aHi bLo bHi aAbsHi bAbsHi
  else add_M1 aLo aHi bLo bHi aAbsHi bAbsHi.

Strategy expand [add_S3 add_S2 add_S add_top add_top2].

Lemma f128_add_split : forall aLo aHi bLo bHi,
  (0 <= aLo < 2^64)%Z -> (0 <= aHi < 2^64)%Z -> (0 <= bLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
  f128_add (aLo + 2^64 * aHi) (bLo + 2^64 * bHi) = add_top aLo aHi bLo bHi.
Proof.
  intros. unfold f128_add. rewrite !lo64_words, !hi64_words by assumption.
  unfold add_top, add_S, add_S2, add_S3. rewrite add_main_split. reflexivity.
Qed.

Definition clz128_w (word hz : Z) : Z := Z.lor (clz64_mirror word) (Z.shiftl hz 6).
Strategy expand [clz128_w].
Lemma clz128_mirror_w : forall hi lo,
  clz128_mirror hi lo = clz128_w (if hi =? 0 then lo else hi) (b2z (hi =? 0)).
Proof. intros. unfold clz128_w. reflexivity. Qed.

Definition norm_w2 (hi lo word hz : Z) : Z * Z * Z :=
  let clz := clz128_w word hz in
  let sh := sub64 clz 15 in
  let '(h, l) := shl128_mirror hi lo sh in
  (h, l, sub64 16 clz).
Strategy expand [norm_w2].
Lemma normalize_mirror_w : forall hi lo,
  normalize_mirror hi lo = norm_w2 hi lo (if hi =? 0 then lo else hi) (b2z (hi =? 0)).
Proof. intros. unfold norm_w2, clz128_w. reflexivity. Qed.

Definition shl128_lo (lo s mask : Z) : Z := Z.land mask (shl64 lo (Z.land s 63)).

Definition normA3 (aHi bHi xHi aSigLo yHi yLo bExp clz sh mask nhi : Z) : Z :=
  add_M3b aHi bHi xHi nhi (shl128_lo aSigLo sh mask) (sub64 16 clz) (Z.land yHi MASK48) yLo bExp.

Definition normB3 (aHi bHi xHi aSigHi aSigLo aExp bSigLo clz sh mask nhi : Z) : Z :=
  add_M4 aHi bHi xHi aSigHi aSigLo aExp nhi (shl128_lo bSigLo sh mask) (sub64 16 clz).

Definition align_4 (xHi subtraction AHi ALo aExp bSigHi3 align mask2 sticky newLo : Z) : Z :=
  let newHi := Z.land mask2 (shr64 bSigHi3 (Z.land align 63)) in
  add_M6 xHi subtraction AHi ALo newHi (Z.lor newLo sticky) aExp.
Definition align_3 (xHi subtraction AHi ALo aExp bSigHi3 bSigLo3 align mask1 negal outHi : Z) : Z :=
  let outLoRaw := shl64 bSigLo3 (Z.land negal 63) in
  let outLo := Z.land mask1 outLoRaw in
  let n2 := zext32 align in
  let sticky := b2z (negb (Z.eqb (Z.lor outLo outHi) 0)) in
  let d2 := sub64 n2 64 in
  let newLo := if is_neg64 d2
               then Z.lor (shr64 bSigLo3 (Z.land align 63)) (shl64 (shl64 bSigHi3 1) (Z.land (not64 n2) 63))
               else shr64 bSigHi3 (Z.land n2 63) in
  align_4 xHi subtraction AHi ALo aExp bSigHi3 align (sra63 d2) sticky newLo.

Definition subR2 (xHi SHi SLo aExp word hz : Z) : Z :=
  let clzS := clz128_w word hz in
  let shiftS := sub64 clzS 12 in
  let '(SHi', SLo') := shl128_mirror SHi SLo shiftS in
  add_M7 xHi SHi' SLo' (sub64 aExp shiftS).
Definition subR3 (xHi SLo aExp shiftS mask nhi : Z) : Z :=
  add_M7 xHi nhi (shl128_lo SLo shiftS mask) (sub64 aExp shiftS).

Definition denorm_3 (signHi hiSh mask4 sticky newLo : Z) : Z :=
  round_mirror (Z.land mask4 hiSh) (Z.lor newLo sticky) 0 signHi.
Definition denorm_2 (signHi SHi SLo shift mask3 t outHi : Z) : Z :=
  let outLo := Z.land mask3 t in
  let hiSh := shr64 SHi (Z.land shift 63) in
  let n3 := zext32 shift in
  let sticky := b2z (negb (Z.eqb (Z.lor outLo outHi) 0)) in
  let d4 := sub64 n3 64 in
  let mask4 := sra63 d4 in
  let newLo := if is_neg64 d4
               then Z.lor (shr64 SLo (Z.land shift 63)) (shl64 (shl64 SHi 1) (Z.land (not64 n3) 63))
               else shr64 SHi (Z.land n3 63) in
  denorm_3 signHi hiSh mask4 sticky newLo.

Definition round_2 (resHi resLo inc : Z) : Z :=
  let sumLo := add64 resLo inc in
  let resHi := add64 resHi (b2z (Z.ltb sumLo resLo)) in
  mk128 resHi sumLo.

Strategy expand [shl128_lo normA3 normB3 align_4 align_3 subR2 subR3 denorm_3 denorm_2 round_2].
