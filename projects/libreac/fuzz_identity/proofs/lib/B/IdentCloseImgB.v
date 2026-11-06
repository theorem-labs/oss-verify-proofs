(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_identity's ASan+UBSan build (image B) from
   proofs/libreac/fuzz_identity/lib/ReusableB/YF0m.v lines 24 and 1576-1633 (a working branch 1ddc6a57e5d,
   sha256 e44564d37ee32f63946a2c422917759b2ed5af6b79bcabbf1c5801a4cbf7efec; TFIB_ERRNO and Tfib_owned_static, copied
   verbatim into this file's lines 50-108, inside Module IdentCloseTables) and from the RO_IN glue of
   proofs/libreac/fuzz_grant/lib/A/AGrantT.v line 47 (a working branch e47e01e8e06; itself from
   proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v, B twin lib/YD2o.v line 42). *)
(* Closing lemmas for four premises that lib/B/IdentTopB.v supplies (:235, :242, :264): HOWN and HERRNO of
   IdentHimgOwned.v:103-104, AJ_NIL_IO of Prog/IdentEntryLink.v:710, and RO_IN. Each conclusion is the premise's type.

   The B core's record is ReusableB/YD2l.v:12 IdentB (the AD2l twin); in this file the record and the core's in_ro_tfa
   are Section variables, and each core fact a lemma needs is a Section premise of exactly the form the core gives:
     TS_OWNED, TS_ERRNO  the fields ts_owned (YF0m.v:1655) and ts_errno (YF0m.v:1646) of the B start-up record
                         TfibSyms, over the frozen Tfib_owned_static and TFIB_ERRNO copied below. The copy sits in
                         its own Module IdentCloseTables, which is never imported, so its two names do not clash
                         with the B core's top-level TFIB_ERRNO / Tfib_owned_static in a file that imports both;
     IN_RO_TFA           the core's definition of in_ro_tfa (fuzz_grant's lib/A/ACeg.v:48, cgif's B twin YCeg.v:42): a
                         disjunction whose right arm is the relro range [0x9b080, 0x9d388).
   With these premises HOWN and HERRNO are the premise itself (the frozen list below and IdentHimgOwned.v:23-80 are
   the same text; both errno words are 0x5d81ac), and RO_IN is or_intror. AJ_NIL_IO takes no core fact: it is
   jl2_nil_io (lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_lit2glue.v:185) at the root's sink head and image instance.
   At the applied B core's IdentB, TS_OWNED and TS_ERRNO hold by eq_refl (or as ts_owned / ts_errno of
   TfibB_syms), and IN_RO_TFA by fun a => eq_refl. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO09 YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym IdentBase IdentRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBImg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentEntryLink.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_lit2glue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B Require IdentHimgOwned.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* IdentTopB.v:161, the link's SEGS at the run ceiling rc. *)
Local Notation SEGSr rc := (@pa_segs _ identb_listing (@PI_identb rc)).

(* ---- the frozen B start-up table: lines 25 and 1578-1635 of lib/ReusableB/YF0m.v, VERBATIM ------------------- *)
(* Its own Module, not imported: the B core defines the same two names at top level. *)
Module IdentCloseTables.
Definition TFIB_ERRNO : Z := 0x5d81ac.
Definition Tfib_owned_static : list (Z * Z) :=
[ (0x9e388, 0xa0c00 - 0x9e388); (0xa0f40, 0xcc0); (0xa1c00, 8); (0xa1c58, 0xa4b08 - 0xa1c58); (0xa4b10, 0x5c7910 - 0xa4b10)    ; (0x5d8250, 0x3c)  ;
(0x9c690, 8); (0x9c6e8, 8);
(0x102e8, 8); (0x10308, 8); (0x10328, 8); (0x103a0, 8); (0x103a8, 8); (0x103b8, 8); (0x10428, 64); (0x10528, 64);
(0x9c670, 0x20); (0x9c698, 0x18); (0x9c6b0, 0x38); (0x9d1f8, 8); (0x9d2e8, 8); (0x9d308, 16); (0x9d370, 16); (0x9d380, 8)  ;
(0x20f82, 0x1e);
(0x20fa3, 0x1d);
(0x20fc7, 0x19);
(0x20fe6, 0x1a);
(0x21024, 0x3c);
(0x21067, 0x19);
(0x21087, 0x19);
(0x210a8, 0x18);
(0x210c5, 0x1b);
(0x21124, 0x3c);
(0x21167, 0x19);
(0x21187, 0x19);
(0x211a8, 0x18);
(0x211c5, 0x1b);
(0x211e3, 0x1d);
(0x21207, 0x19);
(0x21226, 0x1a);
(0x21266, 0x1a);
(0x21297, 0x29);
(0x212c6, 0x1a);
(0x212f6, 0x2a);
(0x21327, 0x19);
(0x21347, 0x19);
(0x2137d, 0x23);
(0x213ac, 0x14);
(0x213dd, 0x23);
(0x21406, 0x1a);
(0x21437, 0x29);
(0x21468, 0x18);
(0x21486, 0x1a);
(0x214b8, 0x28);
(0x214e8, 0x18);
(0x21507, 0x19);
(0x21538, 0x28);
(0x21569, 0x17);
(0x21587, 0x19);
(0x215b8, 0x28);
(0x215e9, 0x17);
(0x21607, 0x19);
(0x21637, 0x29);
(0x21668, 0x18);
(0x21687, 0x19);
(0x216b7, 0x29);
(0x216e8, 0x18);
(0x21707, 0x19);
(0x21738, 0x28);
(0x21768, 0x18);
(0x9b478, 0x28);
(0x9b4b8, 0x28);
(0x9b4f8, 0x28);
(0x9c1d8, 0x328);
(0x5d81f8, 8); (0x5d8248, 8); (0x5d8260, 8)  ; (0x5f95f8, 8);
(0x1ce7f, 21); (0x20d10, 4); (0x21d04, 4); (0x21d68, 2); (0x9d318, 8); (0x5f8510, 8) ].
End IdentCloseTables.

Section own.
(* ReusableB/YD2l.v:12 IdentB, the B core's record. *)
Variable IdentB : asyms.
(* YF0m.v:1655 ts_owned and YF0m.v:1646 ts_errno, the two fields of the B start-up record TfibSyms at IdentB. *)
Hypothesis TS_OWNED : as_owned_static IdentB = IdentCloseTables.Tfib_owned_static.
Hypothesis TS_ERRNO : as_errno IdentB = IdentCloseTables.TFIB_ERRNO.

(* IdentHimgOwned.v:103 HOWN, supplied at IdentTopB.v:235. It is TS_OWNED itself: IdentCloseTables.Tfib_owned_static and
   IdentHimgOwned.TFIB_OWNED_STATIC_B unfold to the same list. *)
Lemma identb_HOWN : as_owned_static IdentB = IdentHimgOwned.TFIB_OWNED_STATIC_B.
Proof. exact TS_OWNED. Qed.

(* IdentHimgOwned.v:104 HERRNO, supplied at IdentTopB.v:235. It is TS_ERRNO itself: IdentCloseTables.TFIB_ERRNO and
   IdentHimgOwned.TFIB_ERRNO_B are both 0x5d81ac. *)
Lemma identb_HERRNO : as_errno IdentB = IdentHimgOwned.TFIB_ERRNO_B.
Proof. exact TS_ERRNO. Qed.

(* IdentTopB.v:242 AJ_NIL_IO: jl2_nil_io (lit2glue.v:185) at the sink head ident_asan_ubsan_sink_head
   (IdentEntryLink.v:68) and the image instance PI_identb (IdentBImg.v:72). *)
Lemma identb_AJ_NIL_IO : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
forall STK sp0 ly S (W : world (SEGSr rc)) mem md own ly' S' W' mem' md' k,
@ajournal rc ident_asan_ubsan_sink_head (SEGSr rc) IdentB STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros fx rc.
exact (@LLVMFuzzerTestOneInput_seg_J_lit2glue.jl2_nil_io rc ident_asan_ubsan_sink_head (@PI_identb rc) IdentB).
Qed.
End own.

Section ro.
(* ReusableB/YCeg.v:31 in_ro_tfa, the B core's definition; in_ro_seg stands for its left arm (the read-only segments). *)
Variable in_ro_tfa : Z -> Prop.
Variable in_ro_seg : Z -> Prop.
(* The core's definition of in_ro_tfa: the read-only segments or the relro range [0x9b080, 0x9d388). *)
Hypothesis IN_RO_TFA : forall a, in_ro_tfa a = (in_ro_seg a \/ (0x9b080 <= a < 0x9d388)).

(* IdentTopB.v:264 Let RO_IN: or_intror, as fuzz_grant's AGrantT.v:47; RLO, RHI = 0x9b080, 0x9d388 (IdentEntryLink.v:76-77). *)
Lemma identb_RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Proof. intros a Ha. rewrite IN_RO_TFA. exact (or_intror Ha). Qed.
End ro.
