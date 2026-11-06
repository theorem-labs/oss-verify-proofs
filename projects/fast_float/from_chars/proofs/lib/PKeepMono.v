(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import RealizesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.

Definition keep_sub (K1 K2 : list ivl) : Prop := forall a, ~ ioutside K1 a -> ~ ioutside K2 a.

Section Mono.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable HS : Type.
Variable Heap : HS -> (word -> option byte) -> Model -> Prop.
Variable blocks : HS -> list (Z * Z).
Variable owned : HS -> list ivl.
Variables GP TP : word.
Variables IMG_LO IMG_END HTOP : Z.
Variable STATIC : list ivl.
Variables K1 K2 : list ivl.
Hypothesis HK : keep_sub K1 K2.

#[using="HK"] Lemma malloc_contract_mono : forall PCM NEED,
  malloc_contract segs cfg HS Heap blocks owned GP TP HTOP K2 PCM NEED ->
  malloc_contract segs cfg HS Heap blocks owned GP TP HTOP K1 PCM NEED.
Proof. LiaFast.lf_pins (fun (HK : LiaFast.U) => LiaFast.u0).
  intros PCM NEED H fx regs m md hs n ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 KC.
  apply (H fx regs m md hs n ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13).
  intros fx' regs' m' md' hs' p C1 C2 C3 C4 C5 C6. apply (KC fx' regs' m' md' hs' p C1 C2 C3 C4 C5).
  intros a Ha. exact (C6 a (HK a Ha)).
Qed.

#[using="HK"] Lemma free_contract_mono : forall PCF NEED,
  free_contract segs cfg HS Heap blocks owned GP TP HTOP K2 PCF NEED ->
  free_contract segs cfg HS Heap blocks owned GP TP HTOP K1 PCF NEED.
Proof. LiaFast.lf_pins (fun (HK : LiaFast.U) => LiaFast.u0).
  intros PCF NEED H fx regs m md hs p k ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 KC.
  apply (H fx regs m md hs p k ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12).
  intros fx' regs' m' md' hs' C1 C2 C3 C4 C5 C6. apply (KC fx' regs' m' md' hs' C1 C2 C3 C4 C5).
  intros a Ha. exact (C6 a (HK a Ha)).
Qed.

#[using="HK"] Lemma fuzz_contract_mono : forall PCZ NEEDZ RO,
  fuzz_contract segs cfg HS Heap blocks GP TP IMG_LO IMG_END HTOP STATIC K2 PCZ NEEDZ RO ->
  fuzz_contract segs cfg HS Heap blocks GP TP IMG_LO IMG_END HTOP STATIC K1 PCZ NEEDZ RO.
Proof. LiaFast.lf_pins (fun (HK : LiaFast.U) => LiaFast.u0).
  intros PCZ NEEDZ RO H fx regs m md hs size ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 KC.
  apply (H fx regs m md hs size ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16).
  intros fx' regs' m' md' hs' C1 C2 C3 C4 C5. apply (KC fx' regs' m' md' hs' C1 C2 C3 C4).
  intros a Ha. exact (C5 a (HK a Ha)).
Qed.
End Mono.

Lemma heap_ok_mono : forall segs cfg HI GP TP IMG_LO IMG_END HTOP STATIC K1 K2 PCM MNEED PCF FNEED, keep_sub K1 K2 ->
  heap_ok segs cfg HI GP TP IMG_LO IMG_END HTOP STATIC K2 PCM MNEED PCF FNEED ->
  heap_ok segs cfg HI GP TP IMG_LO IMG_END HTOP STATIC K1 PCM MNEED PCF FNEED.
Proof.
  intros segs cfg HI GP TP IMG_LO IMG_END HTOP STATIC K1 K2 PCM MNEED PCF FNEED HK (A & B & C & D & E).
  refine (conj A (conj _ (conj _ (conj D E)))).
  - exact (malloc_contract_mono segs cfg _ _ _ _ GP TP HTOP K1 K2 HK PCM MNEED B).
  - exact (free_contract_mono segs cfg _ _ _ _ GP TP HTOP K1 K2 HK PCF FNEED C).
Qed.
