(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are
   restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin image A from
   proofs/libreac/fuzz_knock/lib/A/APgLib.v at origin/ossv/recipes 6ebe35ba632, with its module paths
   changed: lines 59-75 (the sink-head guard and the read-only pair), 123-124
   (knock_lib_contract_x_all), 246-248 (XL0) and 315-371 (the bridge to ACfn's form) are taken in pin's
   names; knock's lines 77-122 (its own copy of the contract text) are NOT taken, because pin's contract
   text is lib/A/PPgCSpec.v's, which image B instantiates as well; knock's lines 126-313 (its journal
   lemmas and its PROOF of the contract) are left out, because pin's walks are P4b's and the proof of
   pin_lib_x_all is P5's. rule 24 (reuse): no function is proved here.

   WHAT THIS FILE GIVES, in the roles knock's lib/A/APgLib.v gives knock_lib_*:
     RO_LO / RO_HI                 pin's read-only pair (knock's 0x96070 / 0x972c8)
     XL0                           the meter argument of the close (knock's lib/A/APgLib.v:246)
     pin_lib_contract_x            PPgCSpec's text at pin's image-A constants
     pin_lib_contract_x_all        it, at every floating-point state
     pin_lib_x_all                 the STATEMENT the close consumes, as a Definition (with knock's LEAF
                                   premise): P4b's walks and P5's close prove
                                   `Theorem pin_lib_x : pin_lib_x_all`
     pin_lib_contract_x_all_tfib   the adapter to lib/A/ACfn.v's form, which lib/A/AD2o.v consumes exactly
                                   as knock's AD2o.v:40-41 consumes knock_lib_contract_x_all_tfib

   THE PIN NUMBERS, measured on the pinned image A (fuzz_pin.asan, sha256
   3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16, section headers of the unstripped twin
   435309a6b12c4d3e09a8484ec253b5fab600e4f00c28694ac28db2fc7a4475ab):
   - RO_LO = 0x97b00 is .data.rel.ro's start and RO_HI = 0x99d48 is .got's end, the pair knock takes
     (.data.rel.ro start .. .got end, the second disjunct of lib/A/ACeh.v's in_ro_tfa). Image B's own pair
     is 0x97c20 .. 0x99e68; image B states its own.
   - PIN_EV_LIB = 2: pin's harness makes ONE malloc and ONE free per call (fuzz/fuzz.h:84-97 fuzz_str and
     fuzz_pin.c:102), and each adds 1 to the event count (lib/Reusable/YG01.v:452 and :460). knock's
     harness makes none, so lib/A/ACfm.v's EV_LIB (knock's value, kept by the relocation) is too small for
     pin; the contract is stated at pin's own budget and bridged to lib/A/ACfn.v's larger one by
     PPgCSpec.pin_lib_contract_x_ev_mono. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACfm AE2k AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require ACfn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YI5b.
(* SINK-HEAD GUARD (knock's lib/A/APgLib.v:59-67): this file's load closure holds the plain build's
   `#[global] Instance src0_sink_head` (lib/Reusable/YI5b.v). It is removed, so no {SK : YI16.sink_head} is
   inferred here or in a file that loads this one. lib/A/AE2k.v's tfib_sink_head (pin's ASan sink head) is
   passed by name at every SK use, so no statement here depends on which instance inference would pick. *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* pin asan .data.rel.ro start .. .got end (section headers), the second disjunct of lib/A/ACeh.v in_ro_tfa *)
Definition RO_LO : Z := 0x97b00.
Definition RO_HI : Z := 0x99d48.
(* pin's harness journal: one malloc and one free *)
Definition PIN_EV_LIB : Z := 2.
(* the meter argument of the close (knock's lib/A/APgLib.v:246) *)
Definition XL0 : Z -> Z := fun _ => 0.
Lemma XL0_HXL : forall n, 0 <= XL0 n.
Proof. intros n. unfold XL0. lia. Qed.

(* ======================= the contract, at pin's image-A constants ======================= *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Definition pin_lib_contract_x : Prop :=
PPgCSpec.pin_lib_contract_x (SK := tfib_sink_head) tfibsegs B MT tfib_K XM_LIB XN_LIB RLO RHI
A_LLVMF RA_LLVMF A_EMPTY PIN_EV_LIB LIVE_LIB LLVMF_STK.
End a.
Definition pin_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @pin_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO RHI.

(* ======================= the statement the close consumes =======================
   STATED, NOT PROVED here: P4b walks the harness and its six callees against lib/A/PPgCSpec.v's contracts
   and P5 closes, as `Theorem pin_lib_x : pin_lib_x_all`. lib/A/AD2o.v then uses that theorem exactly where
   knock's lib/A/AD2o.v:41 uses `@APgLib.knock_lib_x_all rc AgreeKnock.ag_sil_shape (fun _ _ _ => eq_refl)`:
   the premise LEAF below is knock's `Hypothesis LEAF` (lib/A/APgLib.v:281), which knock's theorem takes as
   an argument once its Section closes, and which AD2o passes as `(fun _ _ _ => eq_refl)` at the shape of
   the agreement proof. Without it the statement is not provable at an arbitrary lib_shape, because LIBK is
   a field of lib_shape (lib/Reusable/YO09.v). The meter is ameter_triv, the meter the close really
   instantiates (knock's APgLib.v:305, AD2o.v:39-41). *)
Definition pin_lib_x_all {rc : YM05.RunCeil} {LS : lib_shape} : Prop :=
(forall pl fs (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs [])) ->
pin_lib_contract_x_all TfibB ameter_triv XL0 XL0 RO_LO RO_HI.

(* ======================= the bridge to the core's contract [knock's APgLib.v:315-371] =======================
   The core (lib/A/AD1q.v, AD1m.v) takes the relocated donor contract ACfn.tfib_lib_contract_x_all; this
   file's text is PPgCSpec's at ACfm's constants and pin's own event budget. ACfn's constants are ACfm's
   (both are pin's relocated values), and ACfn's event budget is the donor's larger one, so the two texts
   differ only in that budget, which pin_lib_contract_x_ev_mono bridges. ACfn is Required, not Imported, so
   its names keep the ACfn prefix and the names below stay ACfm's. *)
Lemma pin_consts :
ACfn.A_LLVMF = A_LLVMF /\ ACfn.RA_LLVMF = RA_LLVMF /\ ACfn.A_EMPTY = A_EMPTY /\
ACfn.LIVE_LIB = LIVE_LIB /\ ACfn.LLVMF_STK = LLVMF_STK.
Proof. repeat split; reflexivity. Qed.
Lemma pin_ev_le : PIN_EV_LIB <= ACfn.EV_LIB.
Proof. unfold PIN_EV_LIB, ACfn.EV_LIB. lia. Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Lemma pin_lib_contract_x_tfib :
pin_lib_contract_x B MT XM_LIB XN_LIB RLO RHI -> ACfn.tfib_lib_contract_x B MT XM_LIB XN_LIB RLO RHI.
Proof.
intros HX.
pose proof (PPgCSpec.pin_lib_contract_x_ev_mono (SK := tfib_sink_head) tfibsegs B MT tfib_K
XM_LIB XN_LIB RLO RHI A_LLVMF RA_LLVMF A_EMPTY PIN_EV_LIB ACfn.EV_LIB LIVE_LIB LLVMF_STK
pin_ev_le HX) as HY.
destruct pin_consts as (E1 & E2 & E3 & E4 & E5).
unfold ACfn.tfib_lib_contract_x, ACfn.tfib_lib_pre_x, ACfn.tfib_lib_post_x.
unfold PPgCSpec.pin_lib_contract_x, PPgCSpec.pin_lib_pre_x, PPgCSpec.pin_lib_post_x in HY.
unfold PPgBase.arodata_okP, PPgBase.in_roP in HY.
unfold arodata_okS.
rewrite ?E1, ?E2, ?E3, ?E4, ?E5.
exact HY.
Qed.
End k.
Lemma pin_lib_contract_x_all_tfib {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops)
(XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) :
pin_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI -> ACfn.tfib_lib_contract_x_all B MT XM_LIB XN_LIB RLO RHI.
Proof. intros HX fx. exact (pin_lib_contract_x_tfib (fx := fx) B MT XM_LIB XN_LIB RLO RHI (HX fx)). Qed.
