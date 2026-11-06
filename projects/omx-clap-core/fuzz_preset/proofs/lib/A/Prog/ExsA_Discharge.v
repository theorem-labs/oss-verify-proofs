(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 pin asan 1be0f53d96cb): ex_string's walk at EVERY float state, and
   the two A' stand-ins it discharges, each restated VERBATIM in its consumer's context (the consumers are not
   imported: on the cut both are red by dependency, S8aStr.v through S8aDisp.v:312, S8aItemsTop.v through
   S8aItemsWalk.v:618 / S8aP7b.v:461):
   - STR  of lib/A/Prog/S8aItemsTop.v:103-104 (Section t: Context {fx rc ci cp}, `#[local] Existing Instance prh_img_A`,
     PA := @PI_prog_A rc, SEGS := pa_segs, Variables B ARx SK, Context {RL}, LAWS at cf_head);
   - STRX of lib/A/Prog/S8aStr.v:121 (Section w: Context {fx rc ci cp RL}, PIA := prh_img_A, PA := @PI_prog_A rc,
     Variables B ARx SK, Context {hl}, LAWS at hl): its discharge here takes LAWS at cf_head, so it holds where the
     consumer's hl is cf_head (the composer's instance: S8aItemsTop.v's LAWS, S8aCompose.v).
   Both are the kit text tex_string_specX at L := A_prog_listing, PA := PI_prog_A, PI := prh_img_A and at the consumer's
   own fx / rc / cp / RL (a Context variable each: no instance is chosen here). CfImg is not a parameter of
   tex_string_specX, so the consumers' {ci} does not reach it.
   PORTED from lib/B/Prog/ExsB_Discharge.v (a Theorem Labs lane's B' check of EXV_HYP's eh_string): the same every-fx form; the
   restated consumer texts are A's. No top-level Print / Check / Print Assumptions (the donor's are not carried). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA ExsA_Stmt ExsA_Lib ExsA_Sym ExsA_Exit ExsA_Cont ExsA_LH ExsA_Callee ExsA_Esc ExsA_Hex1 ExsA_Hex1R ExsA_Hex2 ExsA_Hex2R ExsA_Utf8 ExsA_Entry ExHex4RunA ExUtf8RunA ExsA_Main.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExsB_Model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the walk at every float state ---- *)
Section h. Context {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PI_prog_A) B.

Theorem ex_string_holds_A_all : forall fx : YK11.FPState,
  tex_string_specX (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK.
Proof.
intros fx. exact (ex_string_holds_A (fx := fx) B ARx SK LAWS HHEAD PAL).
Qed.
End h.

(* ---- STR of lib/A/Prog/S8aItemsTop.v:103-104, in Section t's context ---- *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {RL : PrhRoomLive}.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.

Lemma es_STR_S8aItemsTop : forall fxc : YK11.FPState,
  tex_string_specX (fx := fxc) (cp := cp) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. exact (ex_string_holds_A_all B ARx SK LAWS HHEAD PAL). Qed.
End t.

(* ---- STRX of lib/A/Prog/S8aStr.v:121, in Section w's context (LAWS at cf_head: see the header) ---- *)
Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation PIA := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.

Lemma es_STRX_S8aStr : forall fx1, tex_string_specX (fx := fx1) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. exact (ex_string_holds_A_all B ARx SK LAWS HHEAD PAL). Qed.
End w.
