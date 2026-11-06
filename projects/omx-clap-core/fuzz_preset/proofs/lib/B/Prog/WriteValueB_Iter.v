(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d), lane of write_value, segment
   WvbIter: THE ITEM LOOP of write_value's container walk, wv_loop: from the loop head (write_value + 4 * 90,
   WriteValueB_Defs.wv_headR at wle' SEGS RZ_cf) at ANY float state to the container's final post wv_Qfin, given the close (wv_CLOSEKR at wle' SEGS RZ_cf) and
   the text at depth n' at every float state (the recursive call), by induction on the items left. Each iteration is
   WriteValueB_IterS's segments (the head, slot 90, through the indent and an object's key to the value's call, and
   after the value, slot 156, to the head at i + 1 or the closing indent and the close, slot 173), chained across the
   two float-state changes of an iteration (put_string and write_value exit at a new float state) by binding each
   segment at the callee's exit float state.
   Contract: WriteValueB_Defs (wv_pre, wv_headR, wv_clR, wv_HEADKR, wv_CLOSEKR, wv_Qfin). Every join of the loop comes
   after one of the container's calls, and a call may realloc, so the loop is stated at wle' SEGS RZ_cf: the
   continuations at that relation, each segment's conclusion SRr' SEGS RZ_cf. No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import WriteValueB_Model WriteValueB_Base
  WriteValueB_Call WriteValueB_Defs WriteValueB_IterL
  WriteValueB_IterS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Set Default Proof Using "All".
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Section f.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
(* image facts of the instance, discharged at PI_prog_B (B_entry_write_value / B_prog_obj_img) *)
Hypothesis Hent : SIGMA AS_write_value = BASE + AF_write_value.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
(* ---- IMAGE FACTS OF THE INSTANCE (discharged at PI_prog_B, WriteValueB_Inst), both read off the generated
   listing ----
   the tag switch's seven table words: each is a ROM word of the read-only band, apart from the GOT word and from
   the shadow-base cell, and inside the image's low range *)
Hypothesis HJT : forall k : nat, (k < 7)%nat ->
  val_mem SEGS (fun _ => None) (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) 4 (WV_JTW k) /\
  0 <= WV_JTW k <= 2 ^ 31 - 1 /\
  0 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k /\
  VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= kLowMemEnd /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 0) \/
   VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + 4 <= VAL (A_OBJ 12) \/
   VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k) /\
  (forall i, 0 <= i < 4 -> in_img SEGS (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     in_roP SEGS pa_relro_lo pa_relro_hi (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i) /\
     ~ Exists (in_zr (VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i)) (as_owned_static B) /\
     ~ (as_errno B <= VAL (A_OBJ 2) + WV_JT + 4 * Z.of_nat k + i < as_errno B + 4)).
(* and the literals: at any state of the run each is a legal put source whose home is kept (put_string's HLIT17
   shape), its bytes being the image's *)
Hypothesis HLIT : forall (k : nat) (bs : list Z) ly' S' Hp' (W' : world SEGS) m' md',
  In (k, bs) wv_lits ->
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' (WV_STR k) bs /\ kept_at B [] (WV_STR k) (Z.of_nat (length bs)) /\
  (forall i, 0 <= i < Z.of_nat (length bs) -> in_img SEGS (WV_STR k + i)).
(* IMAGE FACT (discharged at PI_prog_B, WriteValueB_Inst): no static of alloc.c lies in the read-only band, so
   a journal's image clause keeps the band (the same text as put_string's and pj_write's walks) *)
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_B).

Section cl.
Variable CTX0 : list (list Z).
Hypothesis PUT : forall fx' : YK11.FPState, tput_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis PUTSTR : forall fx' : YK11.FPState, tput_string_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis INDENT : forall fx' : YK11.FPState, tindent_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling; at the instance the allocator-model owner's preset_head_wide):
   a key string handed to put_string is cstr_ok (wvi_cstr_blk) *)
Hypothesis HW : prh_head_wide.

Section cont.
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.

(* WriteValueB_IterS's segments, each bound at the float state its join runs at *)
Let SEG90 (f : YK11.FPState) := @WriteValueB_IterS.wvs_seg_90 f rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let SEG130 (f : YK11.FPState) := @WriteValueB_IterS.wvs_seg_130 f rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.
Let SEG156 (f : YK11.FPState) := @WriteValueB_IterS.wvs_seg_156 f rc ci cp RL SK PA B ARx LAWS TL Hent Hobj HJT HLIT HPSTRO CTX0 PUT PUTSTR INDENT HW Pm PLAW PCALL.

(* THE ITEM LOOP: from the head at item i (any float state) to the container's final post, by induction on the items
   left; an iteration runs the head's segment at the head's float state f, the key's continuation (slot 130) at
   put_string's exit float state, and the value's continuation (slot 156) at write_value's exit float state, which
   goes on to the head at i + 1 there (the induction hypothesis) or to the close (HCL) *)
Lemma wv_loop : forall (n' : nat) (X : wvx) ch,
  (forall fx' : YK11.FPState, twrite_value_specX (fx := fx') (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n') ->
  STK_write_value (S n') <= y_STK X -> (PjTree.depth (y_t X) <= S n')%nat -> wv_pre B ARx CTX0 Pm X ch ->
  wv_CLOSEKR B ARx Pm (wle' SEGS RZ_cf) X -> wv_HEADKR B ARx Pm (wle' SEGS RZ_cf) X.
Proof.
intros n' X ch IH HSTKn Hdn Hpre HCL.
assert (KEY : forall m i, (wv_nitems (y_t X) - i = m)%nat ->
  forall (f : YK11.FPState) P lyc Sc Hpc (Wc : world SEGS) (regsc : bvmap 5 word) memc mdc kc,
    wv_headR B ARx Pm (wle' SEGS RZ_cf) X f i P lyc Sc Hpc Wc regsc memc mdc kc ->
    SRr' SEGS RZ_cf Wc (mkCfg (@mkst f regsc (Z_to_bv 64 (BASE + WVH_PC)) memc (seg_rom SEGS)) mdc)
      (wv_Qfin B ARx Pm X)).
{ induction m as [|m IHm]; intros i Hm f P lyc Sc Hpc Wc regsc memc mdc kc Hh.
  - exfalso. destruct Hh as (_ & Hi & _). lia.
  - assert (Hi : (i < wv_nitems (y_t X))%nat) by (destruct Hh as (_ & Hi & _); exact Hi).
    assert (K156 : WriteValueB_IterS.wvs_K156R B ARx Pm (wle' SEGS RZ_cf) X i).
    { intros f3 ly3 S3 Hp3 W3 regs3 mem3 md3 k3 Hst3.
      exact (SEG156 f3 n' X ch i ly3 S3 Hp3 W3 regs3 mem3 md3 k3 HSTKn Hpre Hi Hst3
        (fun P' lyc' Sc' Hpc' Wc' regs' mem' md' kc' Hh' =>
           IHm (S i) ltac:(lia) f3 P' lyc' Sc' Hpc' Wc' regs' mem' md' kc' Hh')
        HCL). }
    assert (K130 : WriteValueB_IterS.wvs_K130R B ARx Pm (wle' SEGS RZ_cf) X i).
    { intros Ht f2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 Hst2.
      exact (SEG130 f2 n' X ch i ly2 S2 Hp2 W2 regs2 mem2 md2 k2 (IH f2) HSTKn Hdn Hpre Hi Ht Hst2 K156). }
    exact (SEG90 f n' X ch i P lyc Sc Hpc Wc regsc memc mdc kc (IH f) HSTKn Hdn Hpre Hh K130 K156). }
intros f i P lyc Sc Hpc Wc regsc memc mdc kc Hh.
exact (KEY _ i eq_refl f P lyc Sc Hpc Wc regsc memc mdc kc Hh).
Qed.

End cont.
End cl.
End h.
End f.
End d.
