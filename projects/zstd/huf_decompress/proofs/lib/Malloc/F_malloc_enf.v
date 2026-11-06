(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_malloc_enf () := "C47Corelib4Init9Datatypes3fstI47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2eq01".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition enf_off0 (o : mem) (st1 : mstate) (b : aptr) (stride idx : Z) : Z :=
  let q := snd b + (16 + stride * idx) in
  if rdv pans_mem o st1 (fst b, q + -3) =? 0 then Z.land (c_mmap_counter (ctx st1)) 255
  else Z.land (rdv pans_mem o st1 (fst b, q + -2) + 256 * rdv pans_mem o st1 (fst b, q + -2 + 1) + 1) 255.

Definition enf_leaf (o : mem) (st1 : mstate) (g b : aptr) (idx n : Z) (st' : mstate) (p : aptr) : Prop :=
  exists off, 0 <= off /\ 16 * off + n + 4 <= get_stride (get_meta_rec st1 g)
    /\ p = (fst b, snd b + 16 + get_stride (get_meta_rec st1 g) * idx + 16 * off)
    /\ st' = havoc p n (fst (enframe_at st1 g idx n off))
    /\ p = snd (enframe_at st1 g idx n off)
    /\ off = fold_off (enf_off0 o st1 b (get_stride (get_meta_rec st1 g)) idx) ((get_stride (get_meta_rec st1 g) - 4 - n) / 16).

Lemma surj_pair_let {A B C'} (e : A * B) (f : A -> B -> C') : (let '(x, y) := e in f x y) = f (fst e) (snd e).
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_enf ()) ["CANSEC1"] "p'0h01Ah11Bh22C'h31ei001eh41fh51ai011ah61bi021bi031pi041xi051yp;2p;3p;4p200R0g0000R1p4p710p8p201R2P1p4p7210p8g000MR3j25TP1j31Tg000mj30Tg001Jj32Tg001dj44Tg002Dj23Tp202R1f2R4f1R5'5R6f3R7P7\7[R8P3f4R9P7P3f5R3P9P9f0R:P7P5P:O2n2001100000120104105P5A139:A039:O2527P5f6R3P9f8R;f7R<P;P<P5P:C4R=31A0;<=O2,33X63W5P5P:O2n2001103000120101102X48X36X21X12X00P9P7P4P5P:O5W4W3W2X12X00o"). Qed.

End CANSEC1.
